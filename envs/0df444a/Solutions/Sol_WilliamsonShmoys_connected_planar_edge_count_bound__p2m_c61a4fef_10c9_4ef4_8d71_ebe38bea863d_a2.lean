-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_count_bound__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:42:14.034088+00:00
-- url     : https://prove2.me/submissions/2004a1e4-3bf0-4de4-89a6-1efe098f200e

import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hConnected : L.Connected) (hDraw : HasPlanarDrawingOn L) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_simple_edge_bound__p2m_346cbd2e_54dd_4cc1_8c07_090cbf4f0cd3_a1 L hV hConnected hDraw
