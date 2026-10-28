-- Prove2me | solution 1 for TurnTables.Reciprocal.optimal_strike
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:01:37.790853+00:00
-- url     : https://prove2.me/submissions/890c762d-5e1f-45eb-9abd-dc0e4213f2e7

import Mathlib
import Definitions.Def_TurnTables_Reciprocal_Model

open TurnTables.Reciprocal in
theorem solution (P : Params) (hP : P.Standing) :
    ∀ R : Impl, ∀ B : ℝ, 0 ≤ B →
      offerorPriorPay P R B ≤ offerorPriorPay P R (strikeB P) := by
  obtain ⟨hγ0, hγ1, hV1, hV2⟩ := hP
  have hV : 0 < P.V2 := by linarith
  have hγV : P.γ * P.V2 < P.V2 := by nlinarith
  have hγV0 : 0 < P.γ * P.V2 := mul_pos hγ0 hV
  have hsum : ∀ f : Impl → ℝ, ∑ E : Impl, f E = f .part + f .full := by
    intro f
    show ∑ E ∈ ({.part, .full} : Finset Impl), f E = _
    rw [Finset.sum_pair (by decide)]
  intro R B hB
  unfold offerorPriorPay
  rw [hsum, hsum]
  unfold offerorPay strikeB
  have c1 : ¬ (P.γ * P.V2 / 2 < P.γ * P.V2 - P.γ * P.V2 / 2) := by
    intro h; linarith
  have c2 : P.γ * P.V2 / 2 < 1 * P.V2 - P.γ * P.V2 / 2 := by linarith
  by_cases h1 : B < P.γ * P.V2 - B <;> by_cases h2 : B < 1 * P.V2 - B <;>
    cases R <;> simp only [Reciprocates, Impl.val] <;>
    simp only [c1, c2, h1, h2, ite_true, ite_false, if_true, if_false] <;>
    linarith
