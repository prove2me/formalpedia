-- Prove2me | solution 2 for WilliamsonShmoys.maximal_planar_edge_count__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:24:23.347471+00:00
-- url     : https://prove2.me/submissions/22b3d88b-8b62-4469-94ca-a2947b300eda

import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_euler_v2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 = 3 * Fintype.card V :=
  WilliamsonShmoys.planar_drawing_maximal_edge_count_euler_v2 K hK hmax hV
