-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:24:56.793448+00:00
-- url     : https://prove2.me/submissions/c2724161-ca3f-469a-b7be-d35dd98d561e

import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_edge_count_upper_bound M hM hV
