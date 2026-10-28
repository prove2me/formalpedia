-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_card_mono__p2m_984b85e4_975d_4113_b6a1_ecc4fb22400d_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T18:42:44.037253+00:00
-- url     : https://prove2.me/submissions/62debf63-f64d-4bd2-b126-192acef1900d

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (S T : SimpleGraph V)
    (hST : S ≤ T) :
    S.edgeSet.ncard ≤ T.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hST)