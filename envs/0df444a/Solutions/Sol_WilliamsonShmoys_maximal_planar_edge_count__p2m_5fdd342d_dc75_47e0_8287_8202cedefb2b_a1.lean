-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_5fdd342d_dc75_47e0_8287_8202cedefb2b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:18:54.822655+00:00
-- url     : https://prove2.me/submissions/670a03e7-4110-471a-add4-d599113b19a0

import Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hCard : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.edge_maximal_planar_edge_count__p2m_397071d2_54cd_4807_97e7_b4001b0535bd_a2 L hCard hL hmax
