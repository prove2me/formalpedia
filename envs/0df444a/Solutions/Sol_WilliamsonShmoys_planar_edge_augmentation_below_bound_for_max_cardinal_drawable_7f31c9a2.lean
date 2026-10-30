-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_augmentation_below_bound_for_max_cardinal_drawable_7f31c9a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:28:20.775615+00:00
-- url     : https://prove2.me/submissions/625fd1e7-d368-465a-9756-023bc7558766

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_for_edge_augmentation_7f31c9a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hBelow : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      K.edgeSet.ncard < H.edgeSet.ncard := by
  obtain ⟨H, hsub, hDrawH, hcount⟩ :=
    WilliamsonShmoys.planar_triangulation_extension_for_edge_augmentation_7f31c9a2
      K hDraw hCard
  refine ⟨H, hsub, hDrawH, ?_⟩
  omega