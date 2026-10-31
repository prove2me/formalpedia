-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_edge_bound__p2m_41f5a52f_01af_4de8_a0be_72b7b0223cd9_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-10-30T22:31:27.511366+00:00
-- url     : https://prove2.me/submissions/237cf27e-1dfb-423e-a48c-707f644e98aa

import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_bound_repair_3e188728

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hconn : K.Connected) (hdraw : HasPlanarDrawingOn K) (hV : 3 <= Fintype.card V) : K.edgeSet.ncard <= 3 * Fintype.card V - 6 :=
  WilliamsonShmoys.connected_planar_edge_bound_repair_3e188728 K hconn hdraw hV
