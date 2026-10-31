-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_upper__p2m_0b1d558b_5b99_484a_a69e_3ba1af67a959_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:09:16.678294+00:00
-- url     : https://prove2.me/submissions/2fc89e1e-95ea-4be7-b539-e8caa3f09b56

import Theorems.Thm_WilliamsonShmoys_planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hT : HasPlanarDrawingOn T) :
    T.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_graph_edge_count_upper_bound__p2m_03ab0e36_fd73_4929_a651_a82d3a3cc822_a1 T hV hT
