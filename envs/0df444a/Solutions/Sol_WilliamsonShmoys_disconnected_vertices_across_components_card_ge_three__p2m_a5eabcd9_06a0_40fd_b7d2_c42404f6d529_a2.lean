-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_vertices_across_components_card_ge_three__p2m_a5eabcd9_06a0_40fd_b7d2_c42404f6d529_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:46:35.792641+00:00
-- url     : https://prove2.me/submissions/266774f0-2a67-46cd-898d-1af819c0bdf8

import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_strict_extension_separated_pair

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ K.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ K.Reachable u v :=
  WilliamsonShmoys.disconnected_planar_drawing_has_strict_extension_separated_pair K hV hDisconnected
