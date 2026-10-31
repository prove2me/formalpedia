-- Prove2me | solution 2 for WilliamsonShmoys.simple_planar_edge_bound__p2m_02b5c4aa_87bb_4609_924c_f8cb942a1930_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T20:50:22.802988+00:00
-- url     : https://prove2.me/submissions/e9edceb7-206c-44f3-8dbb-cd04064ef0fc

import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_face_accounting_57972424

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V :=
  WilliamsonShmoys.planar_edge_bound_for_face_accounting_57972424 G hG hconn hCard
