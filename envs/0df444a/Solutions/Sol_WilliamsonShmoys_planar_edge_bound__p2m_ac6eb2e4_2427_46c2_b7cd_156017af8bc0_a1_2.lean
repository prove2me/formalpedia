-- Prove2me | solution 2 for WilliamsonShmoys.planar_edge_bound__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:54:41.857357+00:00
-- url     : https://prove2.me/submissions/5025208e-1cc1-40da-9d83-4934a3d53508

import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_upper_bound__p2m_ec135dca_b35f_4690_a88a_60012f6a0abd_a1 G hDraw hCard
