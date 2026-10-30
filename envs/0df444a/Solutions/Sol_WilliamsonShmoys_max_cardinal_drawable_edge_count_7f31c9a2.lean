-- Prove2me | solution 1 for WilliamsonShmoys.max_cardinal_drawable_edge_count_7f31c9a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:07:30.676846+00:00
-- url     : https://prove2.me/submissions/5dc9d280-7378-48b4-9ded-1ebcc10fe801

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_max_cardinal_drawable_7f31c9a2
import Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound_for_max_cardinal_drawable_7f31c9a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hMax : ∀ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet →
      HasPlanarDrawingOn H →
      H.edgeSet.ncard ≤ K.edgeSet.ncard)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  have hUpper :=
    WilliamsonShmoys.planar_edge_count_upper_bound_for_max_cardinal_drawable_7f31c9a2
      K hDraw hCard
  by_contra hEq
  have hStrict : K.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨H, hExt, hDrawH, hCount⟩ :=
    WilliamsonShmoys.planar_edge_augmentation_below_bound_for_max_cardinal_drawable_7f31c9a2
      K hDraw hCard hStrict
  have hMaxH := hMax H hExt hDrawH
  omega