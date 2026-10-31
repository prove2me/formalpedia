-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:26:33.752334+00:00
-- url     : https://prove2.me/submissions/d006e986-492a-4e24-adbc-1168bd412b55

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_repair

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn L) (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V ≤ L.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_repair L hV hDraw hMax
