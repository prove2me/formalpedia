-- Prove2me | solution 1 for WilliamsonShmoys.triangulation_maximal_drawable_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:10:26.5535+00:00
-- url     : https://prove2.me/submissions/93a22b75-8a25-4452-af6b-188932341ebd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_drawing
import Theorems.Thm_WilliamsonShmoys_planar_underfull_edge_augmentation

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  have hbound := WilliamsonShmoys.planar_edge_bound_of_drawing L hV hL
  have hnot_underfull : ¬ L.edgeSet.ncard + 6 < 3 * Fintype.card V := by
    intro hunderfull
    obtain ⟨M, hsub, hneq, hM⟩ :=
      WilliamsonShmoys.planar_underfull_edge_augmentation L hV hL hunderfull
    exact hneq (hmax M hsub hM)
  omega