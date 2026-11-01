-- Prove2me | solution 3 for WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:14:10.060427+00:00
-- url     : https://prove2.me/submissions/914d99a7-4ed1-4475-9f61-8f6658f10814

import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_count_upper_bound__p2m_e5f859ef_036f_4a0e_a441_f58ddfd6756c_a1 L hcard hL
