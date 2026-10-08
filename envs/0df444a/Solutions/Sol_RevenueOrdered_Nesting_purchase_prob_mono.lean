-- Prove2me | solution 1 for RevenueOrdered.Nesting.purchase_prob_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:32:39.247544+00:00
-- url     : https://prove2.me/submissions/88e5418a-956a-41d2-b4b4-beeff34f9141

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_Model

open RevenueOrdered.Nesting in
/-- Lemma 2.1: under a regular discrete choice model the purchase probability does not
decrease when the choice set is enlarged. -/
theorem solution {C : Type*} {P : C → Finset C → ℝ} (hP : RevenueOrdered.Nesting.IsRegular P)
    {S S' : Finset C} (hSS' : S ⊆ S') :
    ∑ x ∈ S, P x S ≤ ∑ x ∈ S', P x S' := by
  have h := hP.noPurchase_mono S S' hSS'
  unfold RevenueOrdered.Ratio.noPurchase at h
  linarith
