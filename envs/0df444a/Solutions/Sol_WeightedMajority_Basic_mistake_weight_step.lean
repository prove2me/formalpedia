-- Prove2me | solution 1 for WeightedMajority.Basic.mistake_weight_step
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:50:29.083499+00:00
-- url     : https://prove2.me/submissions/38aa7883-b3da-41fd-9bb6-2c21e13ce4d1

import Mathlib
import Definitions.Def_WeightedMajority_Basic_IsWMRun

open WeightedMajority.Basic

/-- The per-mistake weight estimate used in the proof of Theorem 2.1. -/
theorem solution {n T : ℕ} (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (initial : Fin n → ℝ) (hinitial : ∀ i, 0 < initial i)
    (x : Fin T → Fin n → Bool) (label : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (prediction : Fin T → Bool)
    (hrun : IsWMRun β initial x label w prediction)
    (t : Fin T) (hmistake : prediction t ≠ label t) :
    totalWeight w (t.val + 1) ≤ ((1 + β) / 2) * totalWeight w t.val := by
  have htot : totalWeight w t.val = voteWeight x w t false + voteWeight x w t true := by
    unfold totalWeight voteWeight
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases x t i <;> simp
  have hup : totalWeight w (t.val + 1) =
      voteWeight x w t (label t) + β * voteWeight x w t (!(label t)) := by
    unfold totalWeight voteWeight
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrun.update]
    cases hl : label t <;> cases hx : x t i <;> simp_all
  have hmajor : voteWeight x w t (label t) ≤ voteWeight x w t (!(label t)) := by
    cases hl : label t
    · by_contra h
      have hp := hrun.predict_zero t (by simpa [hl] using lt_of_not_ge h)
      exact hmistake (hp.trans hl.symm)
    · by_contra h
      have hp := hrun.predict_one t (by simpa [hl] using lt_of_not_ge h)
      exact hmistake (hp.trans hl.symm)
  rw [hup, htot]
  cases hl : label t <;> simp only [hl, Bool.not_false, Bool.not_true] at * <;> nlinarith

#print axioms solution
