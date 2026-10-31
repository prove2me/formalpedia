-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound__p2m_2ba654e2_e4e9_4dba_a1f5_978037f8b005_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T21:43:20.681995+00:00
-- url     : https://prove2.me/submissions/f609502e-04fa-43db-be4a-9c76838d19c5

import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_count_c7059b55_ff77_4f00_a57a_8983712db7a5

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hDraw : HasPlanarDrawingOn S) (hConnected : S.Connected) (hV : 3 <= Fintype.card V) : S.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.planar_drawing_connected_edge_count_c7059b55_ff77_4f00_a57a_8983712db7a5 S hDraw hConnected hV
