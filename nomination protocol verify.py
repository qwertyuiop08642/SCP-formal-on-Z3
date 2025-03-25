from z3 import *
import time
n = 6 # 节点个数
m = 6 # 消息个数
start_time = time.time()
nodes = [f'node{i+1}' for i in range(n)]
Node, node_consts = EnumSort('Node', nodes)
nomis = [f'{i}' for i in range(m)]
Nomi, nomi_consts = EnumSort('Nomi', nomis)

nodes = node_consts
nomis = nomi_consts
nsets = [BitVecVal(i, n) for i in range(2**n)] # 使用位向量表示Nset

in_set = Function('in_set', Node, BitVecSort(n), BoolSort()) # 在集合里 事实上下文通过位向量的比较使得这个函数没有使用
in_qslice = Function('in_qslice', Node, Node, BoolSort()) # 第二个节点在第一个节点的qslice里
well_behave = Function('well_behave', Node, BoolSort()) # 是否为好节点
is_blocking_set = Function('is_blocking_set', Node, BitVecSort(n), BoolSort()) # v-阻塞集 此处无用
is_blocking_point = Function('is_blocking_point', Node, Node, BoolSort()) # 第二个节点时第一个节点的阻塞集 由于只有一个qslice，事实上与in_qslice等价
is_quorum = Function('is_quorum', BitVecSort(n), BoolSort()) # 是否是quorum
# 有关恶意节点
is_dset_c = Function('is_dset_c', BitVecSort(n), BoolSort()) # dset 补 在带量词的形式化中如此实现较为方便，所以此处同意
is_intact = Function('is_intact', Node, BoolSort()) # 是否为完整节点
is_quorum_within = Function('is_quorum_within', BitVecSort(n), BitVecSort(n), BoolSort()) # 第一个集合在第二个集合中为quorum

init_nomi = Function('init_nomi', Node, Nomi, BoolSort()) # 起始提名
nomi = Function('nomi', Node, Nomi, BoolSort()) # 当前提名
ratify = Function('ratify', Node, Nomi, BoolSort()) # 批准
accept = Function('accept', Node, Nomi, BoolSort()) # 接受
confirm = Function('confirm', Node, Nomi, BoolSort()) # 确认
local_vote_nomi = Function('local_vote_nomi', Node, Node, Nomi, BoolSort()) # 第一个节点认为第二个节点给提名vote
local_quorum_ratify = Function('local_quorum_ratify', Node, BitVecSort(n), Nomi, BoolSort()) # 节点认为quorum给ratify提名
local_ratify_nomi = Function('local_ratify_nomi', Node, Node, Nomi, BoolSort()) # 第一个节点认为第二个节点给提名vote
local_accept_nomi = Function('local_accept_nomi', Node, Node, Nomi, BoolSort()) # 第一个节点认为第二个节点给接受vote

# 最后几个谓词表示我们在为每个节点生成了一个本地的观测
# 展平约束
def flatten(l):
    return [s for t in l for s in t]

# 下面是协议的约束实现 我们把量词消除前的约束作为注释放在了每个处理后的约束的前面以便检查

# C1 = [Distinct(nodes)]
# simplify(nodes[1] == nodes[2]) -> False

# 一些定义

# Defi1 = [ in_set(nodes[i], nsets[j]) == Extract(i, i, nsets[j]) for i in range(n) for j in range(2**n)]

Defi2 = [# quorum定义
    # ForAll([nset], And(ForAll([node1], Implies(in_set(node1, nset), ForAll([node2], Implies(in_qslice(node1, node2), in_set(node2, nset))))), Exists([node2], in_set(node2, nset))) ==
    #            is_quorum(nset)),
    [And(And([Implies(Extract(i1, i1, nsets[j]) == 1, And([Implies(in_qslice(nodes[i1], nodes[i2]), Extract(i2, i2, nsets[j]) == 1) for i2 in range(n)])) for i1 in range(n)]), Not(nsets[j] == 0)) == is_quorum(nsets[j]) for j in range(2**n)],
    #v-blocking set 的定义 此处首先假设只有一个qslice
    #   ForAll([node1, node2], in_qslice(node1, node2) == is_blocking_point(node1, node2))
    [in_qslice(nodes[i1], nodes[i2]) == is_blocking_point(nodes[i1], nodes[i2]) for i1 in range(n) for i2 in range(n)],
    # quorum_within
    # ForAll([nset, nset1], And(ForAll([node1], Implies(in_set(node1, nset), And(in_set(node1, nset1), ForAll([node2], Implies(And(in_set(node2, nset1), in_qslice(node1, node2)), in_set(node2, nset)))))), Exists([node3], in_set(node3, nset))),
    #            == is_quorum_within(nset, nset1)),
    [And(And([Implies(Extract(i1, i1, nsets[j]) == 1, And(Extract(i1, i1, nsets[j1]) == 1, And([Implies(And(Extract(i2, i2, nsets[j1]) == 1, in_qslice(nodes[i1], nodes[i2])), Extract(i2, i2, nsets[j]) == 1) for i2 in range(n)]))) for i1 in range(n)]), Not(nsets[j] == 0))
                == is_quorum_within(nsets[j], nsets[j1]) for j in range(2**n) for j1 in range(2**n)],
    # is_dset_c Or([And(in_set(nodes[i1], nsets[j1]), in_set(nodes[i1], nsets[j2])) for i1 in range(n)]) 用 Not(nsets[j1] & nsets[j2] == 0) 替代
    [And(And([Implies(And(is_quorum_within(nsets[j1], nsets[j]), is_quorum_within(nsets[j2], nsets[j])), Not(nsets[j1] & nsets[j2] == 0)) for j1 in range(2**n) for j2 in range(2**n)]), #QI
              Or(is_quorum(nsets[j]), nsets[j] == 0))
                       == is_dset_c(nsets[j]) for j in range(2**n)],
    # intact
    [Or([And(is_dset_c(nsets[j]), Extract(i1, i1, nsets[j]) == 1, And([Implies(Not(well_behave(nodes[i2])), Extract(i2, i2, nsets[j]) == 0) for i2 in range(n)])) for j in range(2**n)])
                       == is_intact(nodes[i1]) for i1 in range(n)],
]
# 问题的一些前提
C1 = [
    # ForAll([node1], in_qslice(node1, node1)), #所有的点在自己的qslice里 好节点特有
    [Implies(well_behave(nodes[i1]), in_qslice(nodes[i1], nodes[i1])) for i1 in range(n)],
    # ForAll([nset, nset1], Implies(And(is_quorum(nset), is_quorum(nset1)), Exists([node1], And(in_set(node1, nset), in_set(node1, nset1))))) #QI
    [Implies(And(is_quorum(nsets[j1]), is_quorum(nsets[j2])), Or([And(Extract(i1, i1, nsets[j1]) == 1, Extract(i1, i1, nsets[j2]) == 1) for i1 in range(n)])) for j1 in range(2**n) for j2 in range(2**n)],
    # 每一个值必须至少被一个人提名 为了保证非平凡性，防止不带条件的提名影响证明结果
    [Or([init_nomi(nodes[i1], x) for i1 in range(n)]) for x in nomis]
]

# 协议实现
# 注意到坏节点的本地存储并不会对系统产生影响，只有最终确认结果可能故意扰乱结果，故只对广播和确认结果加了好节点限定
C2 = [# ForAll([x, node1, node2], Implies(well_behave(node1), Or(init_nomi(nodes[i1], x), nomi(nodes[i1], x)) == local_vote_nomi(node2, node1, x))), #广播起始提名/支持提名 好节点特有
    [Implies(well_behave(nodes[i1]), Or(init_nomi(nodes[i1], x), nomi(nodes[i1], x)) == local_vote_nomi(nodes[i2], nodes[i1], x)) for i1 in range(n) for i2 in range(n) for x in nomis],
      # ForAll([x, node1, node2], Implies(And(local_vote_nomi(node2, node1, x), in_qslice(node2, node1)), nomi(node2, x))), # 若信任，加入自己的提名支持名单
    [Or([And(in_qslice(nodes[i2], nodes[i1]), local_vote_nomi(nodes[i2], nodes[i1], x)) for i1 in range(n)]) == nomi(nodes[i2], x) for i2 in range(n) for x in nomis],
      # ForAll([x, node1, nset], Implies(ForAll([node2], Implies(in_set(node2, nset), local_vote_nomi(node1, node2, x))), local_nset_ratify(node1, nset, x))), # 本地观测决定是否批准
    [And(And([Implies(Extract(i2, i2, nsets[j]) == 1, local_vote_nomi(nodes[i1], nodes[i2], x)) for i2 in range(n)]), is_quorum(nsets[j])) == local_quorum_ratify(nodes[i1], nsets[j], x) for i1 in range(n) for j in range(2**n) for x in nomis],
      # ForAll([x, node1, node2], Implies(Exists([nset], And(in_set(node2, nset), local_nset_ratify(node1, nset, x))), local_ratify_nomi(node1, node2, x))),
    [Or([And(Extract(i2, i2, nsets[j]) == 1, local_quorum_ratify(nodes[i1], nsets[j], x)) for j in range(2**n)]) == local_ratify_nomi(nodes[i1], nodes[i2], x) for i1 in range(n) for i2 in range(n) for x in nomis],
      # ForAll([x, node1], Or(Exists([nset], And(in_set(node1, nset), is_quorum(nset), local_quorum_ratify(node1, nset, x))), Exists([node2], And(is_blocking_point(node1, node2), local_ratify_nomi(node1, node2, x)))) == accept(node1, x)), # 接受流程
    [Or(Or([And(Extract(i1, i1, nsets[j]) == 1, is_quorum(nsets[j]), local_quorum_ratify(nodes[i1], nsets[j], x)) for j in range(2**n)]), Or([And(is_blocking_point(nodes[i1], nodes[i2]), local_ratify_nomi(nodes[i1], nodes[i2], x)) for i2 in range(n)])) == accept(nodes[i1], x) for i1 in range(n) for x in nomis],
      # ForAll([x, node1, node2], Implies(well_behave(node1), accept(node1, x) == local_accept_nomi(node2, node1, x))), # 广播接受提名 好节点特有
    [Implies(well_behave(nodes[i1]), accept(nodes[i1], x) == local_accept_nomi(nodes[i2], nodes[i1], x)) for i1 in range(n) for i2 in range(n) for x in nomis],
      # ForAll([x, node1], Implies(well_behave(node1), Exists([nset], And(in_set(node1, nset), is_quorum(nset), ForAll([node2], Implies(in_set(node2, nset), local_accept_nomi(node1, node2, x))))) == confirm(node1, x))) # 确认流程 好节点特有（坏节点可以随意模拟扰乱结果）
    [Implies(well_behave(nodes[i1]), Or([And(Extract(i1, i1, nsets[j]) == 1, is_quorum(nsets[j]), And([Implies(Extract(i2, i2, nsets[j]) == 1, local_accept_nomi(nodes[i1], nodes[i2], x)) for i2 in range(n)])) for j in range(2**n)]) == confirm(nodes[i1], x)) for i1 in range(n) for x in nomis],
]

# 证明：所有的完整节点的confirm值收敛 也就是说每个完整节点对于每个消息同时confirm或不confirm
S1 = [Implies(And(is_intact(node_consts[i]), is_intact(node_consts[j])), confirm(node_consts[i], x) == confirm(node_consts[j], x)) for i in range(n) for j in range(n) for x in nomi_consts]

finalization_condition = Or([
    And([
        Implies(is_intact(node_consts[i]),
        confirm(node_consts[i], x))
        for i in range(n)
    ])
    for x in nomi_consts
])

s = Solver()
s.add(flatten(Defi2) + flatten(C1) + flatten(C2) + [Not(s) for s in S1])
s.add(Not(finalization_condition))
end_time = time.time()
print(end_time - start_time)
 # 检查反例
if s.check() == unsat:
    print("在最后一个时刻，该值已经被最终外化")
else:
    print("在最后一个时刻，该值未被最终外化")
