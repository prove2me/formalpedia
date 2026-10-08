-- Prove2me | solution 1 for RevenueOrdered.Ratio.purchase_prob_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T03:48:19.669999+00:00
-- url     : https://prove2.me/submissions/b409be9d-e611-4a2f-a93c-f7682715e7ba

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model

open RevenueOrdered.Ratio in
/-- Lemma 2.1 (p. 6): under a regular discrete choice model the probability of making a
purchase does not decrease when the choice set is enlarged. -/
theorem solution {C : Type*} (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P)
    (S S' : Finset C) (hSS' : S ⊆ S') :
    ∑ x ∈ S, P x S ≤ ∑ x ∈ S', P x S' := by
  have h := hP.noPurchase_mono S S' hSS'
  unfold RevenueOrdered.Ratio.noPurchase at h
  linarith
