-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono_repair_20261028
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:36:07.858671+00:00
-- url     : https://prove2.me/submissions/f0b0afbf-c483-4177-a844-d5a45083a484

import Mathlib
theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard :=
  Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hHK) (Set.toFinite _)
