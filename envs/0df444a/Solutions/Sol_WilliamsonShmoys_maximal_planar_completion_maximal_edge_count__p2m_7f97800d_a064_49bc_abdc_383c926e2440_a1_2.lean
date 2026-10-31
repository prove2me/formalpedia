-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_completion_maximal_edge_count__p2m_7f97800d_a064_49bc_abdc_383c926e2440_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:36:50.330703+00:00
-- url     : https://prove2.me/submissions/0831181b-4a16-45ce-a087-f6c96e3030b3

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_v3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hmaximal : forall N : SimpleGraph V, LE.le M N -> WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) (hV : 3 <= Fintype.card V) : M.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_drawable_graph_edge_count_v3 M hMplanar hmaximal hV
