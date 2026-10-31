-- Prove2me | solution 2 for WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_5db12fa6_6ddb_45ce_9ff4_a1f528d0a813_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:46:02.710677+00:00
-- url     : https://prove2.me/submissions/45b003ff-6226-4578-99dd-4c8cf5c16572

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_count_bound__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4 H hH hconn hV
