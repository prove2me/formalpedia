-- Prove2me | solution 1 for WilliamsonShmoys.proper_supergraph_edge_ncard__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:14:01.815314+00:00
-- url     : https://prove2.me/submissions/302074fb-5128-4f9e-98a5-9bb16e3d40c4

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : ∀ u v, H.Adj u v → K.Adj u v)
    (hne : H ≠ K) :
    H.edgeSet.ncard < K.edgeSet.ncard := by
  classical
  have hle : H ≤ K := fun _ _ hadj => hHK _ _ hadj
  have hlt : H < K := lt_of_le_of_ne hle hne
  apply Set.ncard_lt_ncard
  · exact SimpleGraph.edgeSet_strict_mono hlt
  · exact Set.toFinite _