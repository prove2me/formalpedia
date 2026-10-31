-- Prove2me | solution 1 for WilliamsonShmoys.edgeMaximalPlanar_edgeCountLower__p2m_9fa2e1cf_f812_43a2_8937_813b0958a481_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:56:32.113301+00:00
-- url     : https://prove2.me/submissions/94c1ea73-6007-497f-9707-0542a7eb817f

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_repair

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn N) (hMax : ∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) : 3 * Fintype.card V ≤ N.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_repair N hV hDraw hMax
