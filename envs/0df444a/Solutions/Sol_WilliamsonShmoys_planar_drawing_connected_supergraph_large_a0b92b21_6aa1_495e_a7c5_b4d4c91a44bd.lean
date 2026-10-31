-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_supergraph_large_a0b92b21_6aa1_495e_a7c5_b4d4c91a44bd
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:50:03.099611+00:00
-- url     : https://prove2.me/submissions/6c4ffc29-8156-43ce-a461-ac30f4a0d0c7

import Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K :=
  WilliamsonShmoys.planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1 H hplanar hV
