-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_b9be61fe_8c1d_403c_9dc2_d4f84da24c92
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T02:49:50.995564+00:00
-- url     : https://prove2.me/submissions/1c42dfc8-6464-4f58-b405-91da7b9f58ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * (Fintype.card V : Int) - 6 = (M.edgeSet.ncard : Int) := by
  apply le_antisymm
  · exact WilliamsonShmoys.maximal_planar_edge_count_lower_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421 M hV hM hmax
  · exact WilliamsonShmoys.planar_edge_count_upper_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421 M hV hM