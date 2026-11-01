-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_subgraph__p2m_10e5fa50_ae85_4d68_b666_509a03938328_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:19:31.945509+00:00
-- url     : https://prove2.me/submissions/87d4f5c8-f749-45a4-bafc-123ae4aeba05

import Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hGH : G ≤ H) : HasPlanarDrawingOn G :=
  WilliamsonShmoys.planar_drawing_subgraph__p2m_1d8ac9c8_ae9e_4d86_8ce6_dc2f073f2eeb_a1 hGH hH
