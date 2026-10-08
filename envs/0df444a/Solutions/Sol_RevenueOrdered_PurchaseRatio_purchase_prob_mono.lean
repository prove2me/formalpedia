-- Prove2me | solution 1 for RevenueOrdered.PurchaseRatio.purchase_prob_mono
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:58:24.843647+00:00
-- url     : https://prove2.me/submissions/5153a0e3-1dd0-48c1-9b69-3e22f3fc2dd0

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model

set_option autoImplicit false

open RevenueOrdered.Ratio in
/-- Lemma 2.1 (Berbeglia–Joret, p. 6): the purchase probability does not decrease when the
choice set is enlarged. -/
theorem solution {C : Type*} (P : C → Finset C → ℝ) (hP : RevenueOrdered.Ratio.IsRegular P)
    (S S' : Finset C) (hSS' : S ⊆ S') :
    ∑ x ∈ S, P x S ≤ ∑ x ∈ S', P x S' := by
  have h := hP.noPurchase_mono S S' hSS'
  unfold RevenueOrdered.Ratio.noPurchase at h
  linarith
