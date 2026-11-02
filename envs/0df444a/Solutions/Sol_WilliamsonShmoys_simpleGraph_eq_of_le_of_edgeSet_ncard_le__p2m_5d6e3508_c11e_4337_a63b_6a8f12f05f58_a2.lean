-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_eq_of_le_of_edgeSet_ncard_le__p2m_5d6e3508_c11e_4337_a63b_6a8f12f05f58_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:03:56.897254+00:00
-- url     : https://prove2.me/submissions/1845b190-2483-4a84-a0bc-e05cee98b964

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (hGH : G ≤ H)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    G = H := by
  have hsub : G.edgeSet ⊆ H.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hGH
  have hedge : G.edgeSet = H.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub hcard
  exact SimpleGraph.edgeSet_inj.mp hedge