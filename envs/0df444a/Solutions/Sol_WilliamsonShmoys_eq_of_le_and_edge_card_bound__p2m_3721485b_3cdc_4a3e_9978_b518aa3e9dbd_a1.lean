-- Prove2me | solution 1 for WilliamsonShmoys.eq_of_le_and_edge_card_bound__p2m_3721485b_3cdc_4a3e_9978_b518aa3e9dbd_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T18:02:47.495637+00:00
-- url     : https://prove2.me/submissions/820aaafe-1176-42a8-acfa-eb314bc71758

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (T U : SimpleGraph V) (hTU : T ≤ U)
    (hcard : Nat.card U.edgeSet ≤ Nat.card T.edgeSet) : U = T := by
  have hsubset : T.edgeSet ⊆ U.edgeSet := SimpleGraph.edgeSet_mono hTU
  have hcard' : U.edgeSet.ncard ≤ T.edgeSet.ncard := by
    simpa only [← Nat.card_coe_set_eq] using hcard
  have heq : T.edgeSet = U.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsubset hcard'
  have hUT : U ≤ T := by
    intro v w hvw
    have hedge : s(v, w) ∈ U.edgeSet := by
      simpa using hvw
    have hedgeT : s(v, w) ∈ T.edgeSet := by
      rw [← heq] at hedge
      exact hedge
    simpa using hedgeT
  exact le_antisymm hUT hTU
