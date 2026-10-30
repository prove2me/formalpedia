-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_edge_count_v4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T06:52:01.686857+00:00
-- url     : https://prove2.me/submissions/b88f7ab5-2aad-4915-8895-ff400a3d889e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_maximal_drawable_graph_8d131a4d
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound_8d131a4d

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P ≤ N) :
    (N.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  have hup := WilliamsonShmoys.planar_edge_count_upper_bound_for_maximal_drawable_graph_8d131a4d N hdraw hV
  have hlo := WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound_8d131a4d N hdraw hV hmax
  omega