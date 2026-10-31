-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_3e16b919_4c6f_4ffa_b173_33b0ad744e42_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:18:09.251014+00:00
-- url     : https://prove2.me/submissions/f9948874-d9bf-4a73-ab48-5c6f106c7b69

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1 M hV hM
