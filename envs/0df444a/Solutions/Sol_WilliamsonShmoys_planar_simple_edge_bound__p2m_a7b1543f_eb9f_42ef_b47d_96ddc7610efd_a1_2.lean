-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_edge_bound__p2m_a7b1543f_eb9f_42ef_b47d_96ddc7610efd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:40:09.107995+00:00
-- url     : https://prove2.me/submissions/130daa01-a70b-4beb-bb4d-feeaf9af58f3

import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_08a17077_59d5_43fa_bc2a_526ccd70f8a2_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_08a17077_59d5_43fa_bc2a_526ccd70f8a2_a1 H hcard hH