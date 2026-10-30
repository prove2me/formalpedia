-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_via_euler_c27addfb_131a_4167_b7de_c130c93bb2da
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T23:44:30.896416+00:00
-- url     : https://prove2.me/submissions/0485643a-0fb2-4e76-be9b-5c19b7f3cfd5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_count_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_supergraph_edge_count_lower_bound
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ X : SimpleGraph V, W ≤ X →
      WilliamsonShmoys.HasPlanarDrawingOn X → X = W) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by
  have hupper := WilliamsonShmoys.planar_simple_edge_count_upper_bound W hV hW
  have hlower :=
    WilliamsonShmoys.maximal_drawable_supergraph_edge_count_lower_bound W hV hW hmax
  omega