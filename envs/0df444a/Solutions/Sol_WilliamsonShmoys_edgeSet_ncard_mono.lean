-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:30:01.028313+00:00
-- url     : https://prove2.me/submissions/93d2023f-8aa4-4c8b-8174-82b423a49b52

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
