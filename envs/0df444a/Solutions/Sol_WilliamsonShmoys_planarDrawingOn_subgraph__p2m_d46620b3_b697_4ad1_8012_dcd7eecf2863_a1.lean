-- Prove2me | solution 1 for WilliamsonShmoys.planarDrawingOn_subgraph__p2m_d46620b3_b697_4ad1_8012_dcd7eecf2863_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:51:07.563887+00:00
-- url     : https://prove2.me/submissions/6184a05e-4f1c-4be0-b684-8446e1dc4ca3

import Theorems.Thm_WilliamsonShmoys_planar_drawing_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : G ≤ H) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G :=
  WilliamsonShmoys.planar_drawing_mono_9538c7a8_17aa_406f_ad1c_e0bdce92c761 hGH hH
