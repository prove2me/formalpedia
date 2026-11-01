-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_f88e8c23_22a3_4ff9_b09b_4991384a83f2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:33.733496+00:00
-- url     : https://prove2.me/submissions/0717ecff-c0c0-4b18-a254-523adacbc5ba

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_exact_edge_count_completion__p2m_a01716d8_a871_45fb_bee6_57d4a8a808ae_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J.edgeSet ⊆ H.edgeSet) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by
  obtain ⟨K, hsub, hK, hcount⟩ :=
    WilliamsonShmoys.drawable_exact_edge_count_completion__p2m_a01716d8_a871_45fb_bee6_57d4a8a808ae_a1
      H hcard hH
  have heq : K.edgeSet = H.edgeSet := Set.Subset.antisymm (hmax K hsub hK) hsub
  rw [← heq, ← hcount]