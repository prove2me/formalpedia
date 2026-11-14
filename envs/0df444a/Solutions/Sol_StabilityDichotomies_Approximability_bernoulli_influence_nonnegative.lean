-- Prove2me | solution 1 for StabilityDichotomies.Approximability.bernoulli_influence_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:01:54.759036+00:00
-- url     : https://prove2.me/submissions/be143ea1-10b2-460e-b6da-02cc83bd7faf

import Mathlib
noncomputable section
open scoped Classical BigOperators

theorem solution {ι : Type} [Fintype ι]
    (h : (ι → Bool) → ℝ) (hh : Monotone h) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ ∑ i : ι, ∑ x : ι → Bool, (∏ j : ι, if x j then p else 1-p) *
      (h (Function.update x i true) - h (Function.update x i false)) := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro x hx
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro j hj
    split_ifs <;> linarith
  · apply sub_nonneg.mpr
    apply hh
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update, hji]
