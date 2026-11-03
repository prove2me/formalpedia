-- Prove2me | solution 1 for WilliamsonShmoys.WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a4
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-03T03:41:01.529504+00:00
-- url     : https://prove2.me/submissions/d6d3fe5d-dfe7-4171-9eb2-2616b25920f5

import Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a6

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

set_option autoImplicit false
open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hP : HasPlanarDrawingOn P) :
    (letI : DecidableRel P.Adj := Classical.decRel P.Adj;
      P.edgeFinset.card + 6 ≤ 3 * Fintype.card V) :=
  WilliamsonShmoys.WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a6 P hV hP