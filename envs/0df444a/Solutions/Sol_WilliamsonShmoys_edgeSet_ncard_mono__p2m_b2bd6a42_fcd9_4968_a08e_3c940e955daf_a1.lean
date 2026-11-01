-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_b2bd6a42_fcd9_4968_a08e_3c940e955daf_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:13.377943+00:00
-- url     : https://prove2.me/submissions/cd5b8ed6-f889-4513-9bf5-84f1c439b6af

import Mathlib
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V)
    (hsub : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono
    (SimpleGraph.edgeSet_mono
      (SimpleGraph.le_iff_adj.mpr (fun u v huv => hsub huv)))