-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:29:01.406985+00:00
-- url     : https://prove2.me/submissions/5b4d8114-048a-4218-b0ef-fad649cf4fe3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH)