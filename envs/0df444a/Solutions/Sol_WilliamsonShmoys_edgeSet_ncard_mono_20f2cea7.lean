-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_20f2cea7
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T06:57:46.373603+00:00
-- url     : https://prove2.me/submissions/8ebe4002-4026-4cd5-89bf-14efd04cf09e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
