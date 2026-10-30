-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_ceffe8f7_0bd7_41ea_898f_3fe9bc8f26e2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:39:09.117689+00:00
-- url     : https://prove2.me/submissions/dbff1bb5-361f-4f36-98bf-9277b93b305e

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V]
    (P Q : SimpleGraph V)
    (hPQ : P ≤ Q) :
    P.edgeSet.ncard ≤ Q.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hPQ) (Set.toFinite _)
