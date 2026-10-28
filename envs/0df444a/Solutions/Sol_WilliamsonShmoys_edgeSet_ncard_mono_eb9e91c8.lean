-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_eb9e91c8
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:33:27.11576+00:00
-- url     : https://prove2.me/submissions/8209afb9-375c-48b6-b282-ccdffddd2d59

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
