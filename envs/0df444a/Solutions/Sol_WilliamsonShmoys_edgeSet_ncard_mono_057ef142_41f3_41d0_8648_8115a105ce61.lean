-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_057ef142_41f3_41d0_8648_8115a105ce61
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T06:15:50.981893+00:00
-- url     : https://prove2.me/submissions/3dfc3bb6-e86d-4228-824b-399d2ca5ba79

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (h : Set.Subset G.edgeSet H.edgeSet) :
    G.edgeSet.ncard <= H.edgeSet.ncard :=
  Set.ncard_le_ncard h (Set.toFinite _)
