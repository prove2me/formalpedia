-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_21bb1f42_93f8_4aca_8bd1_86213d966802_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:18:24.639063+00:00
-- url     : https://prove2.me/submissions/54e07a1a-9213-45be-861d-c5492ef407de

import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_d1156ce4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = L.edgeSet.ncard + 6 :=
  WilliamsonShmoys.maximal_planar_drawing_edge_count_d1156ce4 L hL hmax hCard
