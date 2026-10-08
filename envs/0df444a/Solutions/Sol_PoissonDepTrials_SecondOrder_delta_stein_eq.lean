-- Prove2me | solution 1 for PoissonDepTrials.SecondOrder.delta_stein_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:30:37.74875+00:00
-- url     : https://prove2.me/submissions/e1f703a5-4d81-4bff-a63d-f1ae01deb84f

import Mathlib
import Definitions.Def_PoissonDepTrials_SecondOrder_Setting

open MeasureTheory ProbabilityTheory Finset

open PoissonDepTrials.SecondOrder in
theorem solution (lam : ℝ) (hlam : 0 < lam) (h : ℕ → ℝ) (M : ℝ) (hM : ∀ k, |h k| ≤ M) :
    ∀ w : ℕ, 1 ≤ w → delta (stein lam h) w =
      -lam⁻¹ * (h w - poissonExp lam h - ((w : ℝ) - lam) * stein lam h w) := by
  intro w hw
  obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  have hl : lam ≠ 0 := hlam.ne'
  unfold delta stein
  rw [Finset.sum_range_succ (n := m + 1)]
  have e1 : m + 1 + 1 - 1 = m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [e1, e2, Nat.factorial_succ]
  push_cast
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  set A := ∑ k ∈ Finset.range (m + 1), (h k - poissonExp lam h) * lam ^ k / (k.factorial : ℝ)
  rw [pow_succ, pow_succ]
  field_simp
  ring
