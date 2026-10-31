-- Prove2me | solution 1 for WilliamsonShmoys.disconnected_pair_of_not_connected__p2m_d5850897_bb19_4a14_84a1_2d0f5ebfaf1b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:29:21.020591+00:00
-- url     : https://prove2.me/submissions/46295ea3-5c09-4400-8201-0f01c957f7cd

import Theorems.Thm_WilliamsonShmoys_disconnected_planar_drawing_has_strict_extension_separated_pair

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDisc : ¬ L.Connected) : ∃ u v : V, u ≠ v ∧ ¬ L.Reachable u v :=
  WilliamsonShmoys.disconnected_planar_drawing_has_strict_extension_separated_pair L hV hDisc
