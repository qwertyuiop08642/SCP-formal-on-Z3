# SCP-formal-on-Z3
This project formally models the core mechanism of the Stellar Consensus Protocol (SCP) and verifies its safety and liveness based on the  Z3-solver. This work was done by @kiwi and collaborators to provide a reproducible automated validation framework for distributed consensus protocols.

We begin by defining variables using bit-vectors and formalizing the protocol rules into a set of first-order logical constraints.  In the uploaded codebase, the _final directory contains the experimentally validated implementation.
