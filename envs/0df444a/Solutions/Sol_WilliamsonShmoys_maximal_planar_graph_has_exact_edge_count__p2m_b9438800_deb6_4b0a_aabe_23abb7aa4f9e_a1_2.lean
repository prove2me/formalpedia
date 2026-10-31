-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_b9438800_deb6_4b0a_aabe_23abb7aa4f9e_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:36:26.909211+00:00
-- url     : https://prove2.me/submissions/882cebd4-ebd6-4766-bf50-891c212fb776

import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) : M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_triangulation_completion_retry3_planar_edge_bound_triangulation_completion_maximal_planar_edge_count M hM hV hMax
