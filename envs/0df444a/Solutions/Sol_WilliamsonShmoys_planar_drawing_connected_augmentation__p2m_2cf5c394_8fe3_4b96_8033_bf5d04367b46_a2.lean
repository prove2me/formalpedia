-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_augmentation__p2m_2cf5c394_8fe3_4b96_8033_bf5d04367b46_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:16:21.02535+00:00
-- url     : https://prove2.me/submissions/32393716-49f7-463f-b9fb-18e3eaf765c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_of_step__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_strict_extension__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    Exists fun H : SimpleGraph V =>
      L <= H /\ H.Connected /\ HasPlanarDrawingOn H := by
  apply WilliamsonShmoys.planar_drawing_connected_augmentation_of_step__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
    L hL
  intro G hLG hG hdisc
  exact WilliamsonShmoys.planar_drawing_disconnected_strict_extension__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
    G hG hcard hdisc
