-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_mono__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:00.70397+00:00
-- url     : https://prove2.me/submissions/1ed70453-804d-4864-aec4-105b1161f1de

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    {L H : SimpleGraph V}
    (hLH : L ≤ H) :
    L.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hLH)