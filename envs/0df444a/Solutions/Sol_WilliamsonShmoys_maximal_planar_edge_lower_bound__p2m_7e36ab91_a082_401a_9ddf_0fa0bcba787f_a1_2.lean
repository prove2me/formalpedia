-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7e36ab91_a082_401a_9ddf_0fa0bcba787f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:00:24.357113+00:00
-- url     : https://prove2.me/submissions/6117aa32-ecad-4800-b682-b91c29736a8b

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_repair

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_repair G hV hG hmax
