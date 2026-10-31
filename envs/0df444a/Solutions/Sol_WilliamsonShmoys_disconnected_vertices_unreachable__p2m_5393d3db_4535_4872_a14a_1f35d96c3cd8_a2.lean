-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_unreachable__p2m_5393d3db_4535_4872_a14a_1f35d96c3cd8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:38:54.839031+00:00
-- url     : https://prove2.me/submissions/53e36935-a3ee-4cc2-af9c-5504a75d5b9f

import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_strict_extension_separated_pair

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisc : ¬ M.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ M.Reachable u v :=
  WilliamsonShmoys.disconnected_planar_drawing_has_strict_extension_separated_pair M hV hDisc
