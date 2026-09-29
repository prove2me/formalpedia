-- Prove2me | solution 1 for TaoFivePrimes.reciprocal_primes_theta_tail_identity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:53:57.180509+00:00
-- url     : https://prove2.me/submissions/53056fb5-05da-40d1-b00d-32aa3565e0ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_reciprocal_primes_theta_partial_summation
import Theorems.Thm_TaoFivePrimes_mertens_constant_theta_integral
import Mathlib
open MeasureTheory Set

theorem solution (x : ℝ) (hx : 2 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) =
      Real.log (Real.log x) +
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
      ((∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x) / (x * Real.log x) -
      ∫ t in Set.Ioi x,
        (((∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)) - t) *
          (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  let θ : ℝ → ℝ := fun t => ∑ p ∈ Nat.primesLE ⌊t⌋₊, Real.log (p : ℝ)
  let R : ℝ → ℝ := fun t => (θ t - t) * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
  let K : ℝ → ℝ := fun t => t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)
  let F : ℝ → ℝ := fun t => Real.log (Real.log t) - 1 / Real.log t
  have hc := TaoFivePrimes.mertens_constant_theta_integral
  change IntegrableOn R (Ioi 2) ∧ _ = _ + ∫ t in Ioi 2, R t at hc
  have hkcont : ContinuousOn K (Icc 2 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    exact ((continuousAt_id.mul ((Real.continuousAt_log ht0).add continuousAt_const)).div
      ((continuousAt_id.pow 2).mul ((Real.continuousAt_log ht0).pow 2))
      (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl0))).continuousWithinAt
  have hkinterval : IntervalIntegrable K volume 2 x := hkcont.intervalIntegrable_of_Icc hx
  have hkint : IntegrableOn K (Ioc 2 x) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mp hkinterval
  have hderiv : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt F (K t) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hloglog := (Real.hasDerivAt_log hl0).comp t (Real.hasDerivAt_log ht0)
    have hinv := (hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_log ht0) hl0
    convert hloglog.sub hinv using 1 <;> (try rfl) <;> (try dsimp [F, K]) <;> field_simp [ht0, hl0] <;> ring
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hkinterval
  rw [intervalIntegral.integral_of_le hx] at hmain
  have hRint : IntegrableOn R (Ioc 2 x) := hc.1.mono_set (by
    intro t ht; exact ht.1)
  have hRx : IntegrableOn R (Ioi x) := hc.1.mono_set (by
    intro t ht; exact lt_of_le_of_lt hx ht)
  have hdisj : Disjoint (Ioc (2 : ℝ) x) (Ioi x) := by
    apply disjoint_left.mpr
    intro t ht hu
    exact (not_lt_of_ge ht.2) hu
  have hsets : Ioc (2 : ℝ) x ∪ Ioi x = Ioi 2 := by
    ext t
    constructor
    · intro ht
      rcases ht with ht | ht
      · exact ht.1
      · exact lt_of_le_of_lt hx ht
    · intro ht
      by_cases htx : t ≤ x
      · exact Or.inl ⟨ht, htx⟩
      · exact Or.inr (lt_of_not_ge htx)
  have hsplit := setIntegral_union hdisj measurableSet_Ioi hRint hRx
  rw [hsets] at hsplit
  have hsumint : (∫ t in Ioc (2 : ℝ) x, θ t * (Real.log t + 1) /
      (t ^ 2 * (Real.log t) ^ 2)) = (∫ t in Ioc (2 : ℝ) x, R t) +
      ∫ t in Ioc (2 : ℝ) x, K t := by
    rw [← integral_add hRint hkint]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp [R, K]
    ring
  have hpartial := TaoFivePrimes.reciprocal_primes_theta_partial_summation x hx
  change (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) = θ x / (x * Real.log x) +
    ∫ t in Ioc (2 : ℝ) x, θ t * (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) at hpartial
  rw [hsumint] at hpartial
  have hx0 : x ≠ 0 := by linarith
  have hl0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have hend : θ x / (x * Real.log x) = (θ x - x) / (x * Real.log x) + 1 / Real.log x := by
    field_simp [hx0, hl0]
    <;> ring
  rw [hend] at hpartial
  dsimp [F] at hmain
  change (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) = _ + (θ x - x) / (x * Real.log x) - ∫ t in Ioi x, R t
  linarith [hc.2]
