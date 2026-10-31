-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_08a17077_59d5_43fa_bc2a_526ccd70f8a2_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:10:31.713396+00:00
-- url     : https://prove2.me/submissions/ff80de98-d691-44f1-a01f-a42a2e7dbdf7

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : HasPlanarDrawingOn H) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1 H hV hH
