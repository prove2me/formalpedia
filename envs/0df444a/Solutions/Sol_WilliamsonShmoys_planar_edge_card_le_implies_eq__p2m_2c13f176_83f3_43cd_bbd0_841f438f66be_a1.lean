-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_card_le_implies_eq__p2m_2c13f176_83f3_43cd_bbd0_841f438f66be_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T20:10:25.404463+00:00
-- url     : https://prove2.me/submissions/73c85ea2-7f26-48e5-b3e7-1508e507edd1

import Theorems.Thm_WilliamsonShmoys_simpleGraph_eq_of_edgeSet_ncard_le__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K L : SimpleGraph V) (hKL : K ≤ L) (hcard : L.edgeSet.ncard ≤ K.edgeSet.ncard) : L = K :=
  WilliamsonShmoys.simpleGraph_eq_of_edgeSet_ncard_le__p2m_ff556b08_9bb8_4b65_af48_6c1ba6d375a5_a1 K L hKL hcard