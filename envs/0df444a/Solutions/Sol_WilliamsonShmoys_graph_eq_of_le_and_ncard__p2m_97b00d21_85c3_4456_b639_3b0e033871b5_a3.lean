-- Prove2me | solution 1 for WilliamsonShmoys.graph_eq_of_le_and_ncard__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:34:28.093294+00:00
-- url     : https://prove2.me/submissions/11466dfb-dccc-488b-9af1-2eb3de37fe1a

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    {L M : SimpleGraph V}
    (hLM : L ≤ M) (hcard : M.edgeSet.ncard ≤ L.edgeSet.ncard) : M = L := by
  classical
  have hsub : L.edgeSet ⊆ M.edgeSet :=
    SimpleGraph.edgeSet_subset_edgeSet.mpr hLM
  have heq : L.edgeSet = M.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub hcard
  exact SimpleGraph.edgeSet_inj.mp heq.symm