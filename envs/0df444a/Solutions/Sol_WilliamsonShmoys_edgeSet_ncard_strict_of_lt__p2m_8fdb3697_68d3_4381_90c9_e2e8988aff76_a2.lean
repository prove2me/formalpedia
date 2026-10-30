-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_strict_of_lt__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:55:29.170501+00:00
-- url     : https://prove2.me/submissions/cac4b0a0-47fc-499f-af0f-3d0832682419

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] (G N : SimpleGraph V)
    (hGN : G ≤ N) (hne : G ≠ N) :
    Set.ncard G.edgeSet < Set.ncard N.edgeSet := by
  classical
  apply Set.ncard_lt_ncard ?_ (Set.toFinite _)
  refine ⟨SimpleGraph.edgeSet_subset_edgeSet.mpr hGN, ?_⟩
  intro hNG
  apply hne
  exact le_antisymm hGN (SimpleGraph.edgeSet_subset_edgeSet.mp hNG)