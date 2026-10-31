-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_419df074_7ffa_4f7d_9922_608f3a25f504_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:51:08.58282+00:00
-- url     : https://prove2.me/submissions/5443ee13-6d33-4957-8353-c06378b93707

import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_edge_count

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) : 3 * Fintype.card V - 6 = H.edgeSet.ncard :=
  WilliamsonShmoys.planar_maximal_supergraph_edge_count H hDraw hV hmax
