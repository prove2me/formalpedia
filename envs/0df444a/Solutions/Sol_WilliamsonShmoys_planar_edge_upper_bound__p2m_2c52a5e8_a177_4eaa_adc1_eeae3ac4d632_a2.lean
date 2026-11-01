-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_2c52a5e8_a177_4eaa_adc1_eeae3ac4d632_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:11:16.205778+00:00
-- url     : https://prove2.me/submissions/3c06c74c-0f84-4aa9-b0f5-e9255012277a

import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) : M.edgeSet.ncard + 6 <= 3 * Fintype.card V :=
  WilliamsonShmoys.planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1 M hcard hplanar
