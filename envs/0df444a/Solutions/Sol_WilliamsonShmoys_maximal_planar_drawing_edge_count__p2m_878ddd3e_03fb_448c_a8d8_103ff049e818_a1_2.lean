-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:37:16.21999+00:00
-- url     : https://prove2.me/submissions/8a75aa9b-1dc1-44c6-9e23-2d105d439fac

import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count_9064c577_retry3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard = 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.maximal_planar_supergraph_edge_count_9064c577_retry3 K hK hmax hV
