-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_triangulation_edgeSet_ncard_mono
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:16:18.394629+00:00
-- url     : https://prove2.me/submissions/7204e7c4-ecfd-410a-87f9-69856677b3c2

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : ∀ ⦃u v⦄, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  have hsub : G.edgeSet ⊆ H.edgeSet := by
    exact SimpleGraph.edgeSet_mono (show G ≤ H from fun _ _ h => hGH h)
  have hfinite : H.edgeSet.Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  exact Set.ncard_le_ncard hsub hfinite