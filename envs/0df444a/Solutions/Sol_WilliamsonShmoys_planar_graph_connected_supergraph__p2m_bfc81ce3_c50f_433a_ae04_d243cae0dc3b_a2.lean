-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:41:40.353019+00:00
-- url     : https://prove2.me/submissions/079c37b0-51dd-4b4a-8dc4-2475fb9fb9fb

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) : ∃ U : SimpleGraph V, T ≤ U ∧ U.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn U :=
  WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c262075_af7a_40b5_8216_f56b847d81a6_a3 T hV hT
