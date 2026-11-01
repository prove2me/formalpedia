-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_mono__p2m_c61a4fef_10c9_4ef4_8d71_ebe38bea863d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T05:13:11.979009+00:00
-- url     : https://prove2.me/submissions/3a4004f5-6b11-4220-9c6d-972c2b4b7750

import Theorems.Thm_WilliamsonShmoys_edge_ncard_mono__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
import Mathlib

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L H : SimpleGraph V) (hLH : L ≤ H) : L.edgeSet.ncard ≤ H.edgeSet.ncard :=
  WilliamsonShmoys.edge_ncard_mono__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2 hLH
