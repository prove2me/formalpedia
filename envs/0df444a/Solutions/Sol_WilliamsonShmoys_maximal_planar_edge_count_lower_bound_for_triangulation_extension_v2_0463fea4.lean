-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_for_triangulation_extension_v2_0463fea4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T13:32:58.570215+00:00
-- url     : https://prove2.me/submissions/8c7f54d7-76ce-4eaa-aaad-ecdcc0ba8bb0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_extension_below_bound

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : forall S : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn S ->
      Set.Subset R.edgeSet S.edgeSet ->
      S.edgeSet = R.edgeSet) :
    3 * Fintype.card V <= R.edgeSet.ncard + 6 := by
  by_contra h
  have hlt : R.edgeSet.ncard + 6 < 3 * Fintype.card V := by omega
  obtain ⟨S, hS, hSub, hNe⟩ :=
    WilliamsonShmoys.planar_edge_extension_below_bound R hCard hR hlt
  exact hNe (hmax S hS hSub)
