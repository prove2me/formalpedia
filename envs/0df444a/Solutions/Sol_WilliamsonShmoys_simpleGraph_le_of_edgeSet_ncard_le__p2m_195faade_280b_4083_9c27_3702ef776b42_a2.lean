-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_le_of_edgeSet_ncard_le__p2m_195faade_280b_4083_9c27_3702ef776b42_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:09:32.534522+00:00
-- url     : https://prove2.me/submissions/1ca2b352-c61e-4af9-9cbe-2b85ac1cba4a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R S : SimpleGraph V) (hRS : R ≤ S)
    (hcard : S.edgeSet.ncard ≤ R.edgeSet.ncard) : S ≤ R := by
  have hsub : R.edgeSet ⊆ S.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hRS
  have hedge : R.edgeSet = S.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub hcard
  exact SimpleGraph.edgeSet_subset_edgeSet.mp (by simpa [hedge])