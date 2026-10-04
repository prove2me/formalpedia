-- Prove2me | solution 1 for TaoFivePrimes.major_arc_sums
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-19T07:16:58.152959+00:00
-- url     : https://prove2.me/submissions/43c0270b-4cf2-41db-b8f7-59ea7ab009f3

import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
Counterexample to the unrestricted formal statement of TaoFivePrimes.major_arc_sums.
The positive-scale major-arc estimate is not contradicted: the witness has x = -1.
The normalized bump construction and its analytic facts are Mathlib's.
-/

open MeasureTheory TaoFivePrimes

set_option autoImplicit false

noncomputable section

theorem solution : ¬ (∀ (η : ℝ → ℝ) (c c' x α : ℝ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hnonneg : ∀ y, 0 ≤ η y)
    (hsupp : ∀ y, η y ≠ 0 → y ∈ Set.Icc c c')
    (hcx : (10 : ℝ) ^ 3 ≤ c * x)
    (hα : |α| ≤ 3.29 * 10 ^ 9 / (4 * Real.pi * c' * x)),
    ‖smoothedExpSum η 1 x α - (x : ℂ) * ∫ y : ℝ, (η y : ℂ) * expCircle (α * x * y)‖ ≤
      (60 * (∫ y, |η y|) + 32 * c' * (∫ y, |deriv η y|)
          + 4 * c' ^ 2 * (∫ y, |deriv (deriv η) y|))
        * (Real.log (3.29 * 10 ^ 9) / (3 * (3.29 * 10 ^ 9))) * x
      + 2.01 / Real.sqrt c * Real.sqrt x
          * ({s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
                riemannZeta s = 0}.ncard : ℝ)
          * (∫ y, |η y|)) := by
  intro h
  let b : ContDiffBump (-1 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let η : ℝ → ℝ := b.normed volume
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) η := b.contDiff_normed
  have hnonneg : ∀ y, 0 ≤ η y := b.nonneg_normed
  have hsupp : ∀ y, η y ≠ 0 → y ∈ Set.Icc (-1000 : ℝ) 0 := by
    intro y hy
    have hym : y ∈ Function.support (b.normed volume) := hy
    rw [b.support_normed_eq] at hym
    change y ∈ Metric.ball (-1 : ℝ) 1 at hym
    rw [Metric.mem_ball, Real.dist_eq] at hym
    rcases abs_lt.mp hym with ⟨hl, hu⟩
    constructor <;> linarith
  have hmass : (∫ y, |η y|) = 1 := by
    simp_rw [abs_of_nonneg (hnonneg _)]
    exact b.integral_normed
  have hbad := h η (-1000) 0 (-1) 0 hsmooth hnonneg hsupp
    (by norm_num) (by norm_num)
  have hsqrt : Real.sqrt (-1 : ℝ) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (by norm_num)
  simp only [hmass, mul_one, mul_zero, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0),
    add_zero, hsqrt] at hbad
  have hlog : 0 < Real.log (3.29 * 10 ^ 9 : ℝ) := Real.log_pos (by norm_num)
  have hpositive : 0 < 60 * (Real.log (3.29 * 10 ^ 9 : ℝ) /
      (3 * (3.29 * 10 ^ 9))) :=
    mul_pos (by norm_num) (div_pos hlog (by norm_num))
  have hnonnegative := le_trans (norm_nonneg _) hbad
  nlinarith
