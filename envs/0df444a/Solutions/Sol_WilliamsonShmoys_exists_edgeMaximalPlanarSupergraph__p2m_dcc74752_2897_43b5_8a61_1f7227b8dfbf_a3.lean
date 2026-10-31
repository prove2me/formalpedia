-- Prove2me | solution 1 for WilliamsonShmoys.exists_edgeMaximalPlanarSupergraph__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:26:43.440588+00:00
-- url     : https://prove2.me/submissions/42406c0d-4e08-4ef5-94a5-0fd4b623cd16

import Theorems.Thm_WilliamsonShmoys_exists_edgeMaximalPlanarSupergraph__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) : ∃ N : SimpleGraph V, G ≤ N ∧ HasPlanarDrawingOn N ∧ (∀ M : SimpleGraph V, N ≤ M → HasPlanarDrawingOn M → M = N) :=
  WilliamsonShmoys.exists_edgeMaximalPlanarSupergraph__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a3__p2m_dcc74752_2897_43b5_8a61_1f7227b8dfbf_a4 G hDraw
