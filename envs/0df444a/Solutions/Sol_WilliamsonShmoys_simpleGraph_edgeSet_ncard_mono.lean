-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T01:00:04.378607+00:00
-- url     : https://prove2.me/submissions/dfde0e06-dff5-4ddd-97ca-2477f9be1ba6

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGH) (Set.toFinite _)
