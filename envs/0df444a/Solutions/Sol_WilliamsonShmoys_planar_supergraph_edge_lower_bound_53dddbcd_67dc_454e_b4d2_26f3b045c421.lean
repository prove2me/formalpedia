-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_lower_bound_53dddbcd_67dc_454e_b4d2_26f3b045c421
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T03:24:06.902177+00:00
-- url     : https://prove2.me/submissions/42c8709e-bc48-4210-b2e2-3e830ff81d86

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_a564c908_f139_469a_b89f_75ea35d29efc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_simple_graph_edge_count_lower_bound_a564c908_f139_469a_b89f_75ea35d29efc

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ N : SimpleGraph V, G <= N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      3 * (Fintype.card V : Int) - 6 <= (N.edgeSet.ncard : Int) := by
  obtain ⟨N, hGN, hN, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_supergraph_a564c908_f139_469a_b89f_75ea35d29efc G hG
  exact ⟨N, hGN, hN,
    WilliamsonShmoys.maximal_planar_simple_graph_edge_count_lower_bound_a564c908_f139_469a_b89f_75ea35d29efc N hV hN hmax⟩