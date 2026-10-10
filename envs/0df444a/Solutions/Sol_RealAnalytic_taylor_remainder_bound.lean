-- Prove2me | solution 1 for RealAnalytic.taylor_remainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:11:33.249711+00:00
-- url     : https://prove2.me/submissions/40e8df69-b012-4395-9b7d-fc5f33291d0c

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

open scoped ContDiff
open Set
set_option autoImplicit false

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} {x h : E} {r : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball x r))
    (hh : ‖h‖ < r) {k : ℕ} (hk : 1 ≤ k) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ y ∈ Metric.ball x r, ‖iteratedFDeriv ℝ k f y‖ ≤ M) :
    ‖f (x + h) - ∑ j ∈ Finset.range k,
      ((j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f x) (fun _ => h)‖ ≤
      M / (k.factorial : ℝ) * ‖h‖ ^ k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  let a : ℝ →ᴬ[ℝ] E := ContinuousAffineMap.const ℝ ℝ x +
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) h).toContinuousAffineMap
  have ha (t : ℝ) : a t = x + t • h := rfl
  have ha1 : a.contLinear 1 = h := by simp [a]
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, a t ∈ Metric.ball x r := by
    intro t ht
    rw [ha, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg h) ht.2).trans_lt hh
  have hs : UniqueDiffOn ℝ (Metric.ball x r) := Metric.isOpen_ball.uniqueDiffOn
  have hp := ((hf.ftaylorSeriesWithin hs).comp_continuousAffineMap a).mono hmem
  have hg : ContDiffOn ℝ ∞ (f ∘ a) (Icc (0 : ℝ) 1) := hp.contDiffOn
  have hd (j : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin j (f ∘ a) (Icc (0 : ℝ) 1) t =
        iteratedFDeriv ℝ j f (a t) (fun _ => h) := by
    rw [iteratedDerivWithin,
      ← hp.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast le_top)
        (uniqueDiffOn_Icc zero_lt_one) ht]
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ha1]
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hs
      (hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hmem t ht)) |>.of_le
        (by exact_mod_cast le_top)) (hmem t ht)]
  have hpoly : taylorWithinEval (f ∘ a) n (Icc (0 : ℝ) 1) 0 1 =
      ∑ j ∈ Finset.range (n + 1),
        ((j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f x) (fun _ => h) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hd j 0 (by simp)]
    simp [ha]
  have hrem := taylor_integral_remainder (f := f ∘ a) (x₀ := 0) (x := 1) (n := n)
    (by simpa only [uIcc_of_le zero_le_one] using
      hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n + 1)))
  rw [uIcc_of_le zero_le_one, hpoly] at hrem
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin (n + 1) (f ∘ a) (Icc (0 : ℝ) 1) t‖ ≤
        M * ‖h‖ ^ (n + 1) := by
    rw [hd (n + 1) t ht]
    exact (ContinuousMultilinearMap.le_opNorm _ _).trans (by
      simpa using mul_le_mul_of_nonneg_right (hb (a t) (hmem t ht))
        (pow_nonneg (norm_nonneg h) (n + 1)))
  have hint : IntervalIntegrable (fun t : ℝ =>
      ((1 - t) ^ n / (n.factorial : ℝ)) * (M * ‖h‖ ^ (n + 1)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (f := fun t : ℝ => ((1 - t) ^ n / (n.factorial : ℝ)) •
      iteratedDerivWithin (n + 1) (f ∘ a) (Icc (0 : ℝ) 1) t)
    (g := fun t : ℝ => ((1 - t) ^ n / (n.factorial : ℝ)) *
      (M * ‖h‖ ^ (n + 1)))
    (Filter.Eventually.of_forall (fun t (ht : t ∈ Ioc (0 : ℝ) 1) => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) n) (Nat.cast_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hbound t ⟨ht.1.le, ht.2⟩)
        (div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) n) (Nat.cast_nonneg _)))) hint
  have heval : (∫ t in (0 : ℝ)..1,
      ((1 - t) ^ n / (n.factorial : ℝ)) * (M * ‖h‖ ^ (n + 1))) =
      M / ((n + 1).factorial : ℝ) * ‖h‖ ^ (n + 1) := by
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) 1]
    simp only [sub_self, sub_zero, integral_pow, one_pow, zero_pow (by omega : n + 1 ≠ 0),
      sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      mul_inv_rev, div_eq_mul_inv]
    ring
  rw [← hrem, heval] at hi
  simpa [Function.comp_def, ha] using hi
