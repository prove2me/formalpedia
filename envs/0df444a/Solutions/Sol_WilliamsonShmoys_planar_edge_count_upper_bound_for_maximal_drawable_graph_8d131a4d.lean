-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_for_maximal_drawable_graph_8d131a4d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:38:38.155208+00:00
-- url     : https://prove2.me/submissions/5e2cbcfa-c83a-48be-8fc7-2094d3330b07

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_exists_8d131a4d
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_bound_8d131a4d

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    (N.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨H, hNH, hHdraw, hCount, hHmax⟩ :=
    WilliamsonShmoys.maximal_drawable_supergraph_exists_8d131a4d N hdraw
  have hBound :=
    WilliamsonShmoys.maximal_drawable_graph_edge_bound_8d131a4d H hHdraw hV hHmax
  exact hCount.trans hBound