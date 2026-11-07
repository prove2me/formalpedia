-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat20_sinc_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:23:45.256653+00:00
-- url     : https://prove2.me/submissions/b73837b2-3a11-450e-862d-8e3353da86cc

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Quantitative upper bound on `sin` over `[0, π]`: `sin x ≤ x - (2/(3π²)) x³`.
Obtained by integrating the quadratic upper bound `cos t ≤ 1 - (2/π²) t²`. -/
private lemma leanlevy_chat20_sin_le_sub_cube {x : ℝ} (hx0 : 0 ≤ x) (hxπ : x ≤ π) :
    Real.sin x ≤ x - 2 / (3 * π ^ 2) * x ^ 3 := by
  have hcos : (∫ t in (0 : ℝ)..x, Real.cos t) = Real.sin x := by
    rw [integral_cos]; simp
  have hint_g : IntervalIntegrable (fun t : ℝ => 1 - 2 / π ^ 2 * t ^ 2) volume 0 x :=
    (by fun_prop : Continuous fun t : ℝ => 1 - 2 / π ^ 2 * t ^ 2).intervalIntegrable 0 x
  have hmono : (∫ t in (0 : ℝ)..x, Real.cos t)
      ≤ ∫ t in (0 : ℝ)..x, (1 - 2 / π ^ 2 * t ^ 2) := by
    refine intervalIntegral.integral_mono_on hx0
      (Real.continuous_cos.intervalIntegrable 0 x) hint_g (fun t ht => ?_)
    have htabs : |t| ≤ π := by rw [abs_of_nonneg ht.1]; exact ht.2.trans hxπ
    exact Real.cos_le_one_sub_mul_cos_sq htabs
  have hval : (∫ t in (0 : ℝ)..x, (1 - 2 / π ^ 2 * t ^ 2))
      = x - 2 / (3 * π ^ 2) * x ^ 3 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((by fun_prop : Continuous fun t : ℝ => 2 / π ^ 2 * t ^ 2).intervalIntegrable 0 x),
        intervalIntegral.integral_const_mul, integral_pow, intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one, sub_zero]
    ring
  calc Real.sin x = ∫ t in (0 : ℝ)..x, Real.cos t := hcos.symm
    _ ≤ ∫ t in (0 : ℝ)..x, (1 - 2 / π ^ 2 * t ^ 2) := hmono
    _ = x - 2 / (3 * π ^ 2) * x ^ 3 := hval

/-- Numeric inequality supporting the lower bound in the large-`|x|` regime:
`2/(3π²) ≤ 1 - 1/π`. -/
private lemma leanlevy_chat20_sinc_lower_const : 2 / (3 * π ^ 2) ≤ 1 - π⁻¹ := by
  have hπ := Real.pi_gt_three
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * π ^ 2)]
  have hprod : (1 - π⁻¹) * (3 * π ^ 2) = 3 * π ^ 2 - 3 * π := by
    field_simp
  rw [hprod]
  nlinarith [hπ, Real.pi_pos]

/-- Two-sided lower bound: `(2/(3π²)) · min(1, x²) ≤ 1 - Real.sinc x` for all `x`. -/
theorem solution (x : ℝ) :
    2 / (3 * π ^ 2) * min 1 (x ^ 2) ≤ 1 - Real.sinc x := by
  have hsinc : Real.sinc x = Real.sinc |x| := by
    rcases abs_choice x with h | h <;> simp [h, Real.sinc_neg]
  rw [hsinc, show x ^ 2 = |x| ^ 2 from (sq_abs x).symm]
  set y := |x| with hy
  have hy0 : 0 ≤ y := abs_nonneg x
  by_cases hy00 : y = 0
  · rw [hy00]; simp
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy00)
    have hcpos : (0 : ℝ) ≤ 2 / (3 * π ^ 2) := by positivity
    rcases le_or_gt y π with hyπ | hyπ
    · have hsin := leanlevy_chat20_sin_le_sub_cube hy0 hyπ
      have hkey : 2 / (3 * π ^ 2) * y ^ 2 ≤ 1 - Real.sinc y := by
        rw [Real.sinc_of_ne_zero hypos.ne',
            show (1 : ℝ) - Real.sin y / y = (y - Real.sin y) / y from by field_simp,
            le_div_iff₀ hypos]
        nlinarith [hsin]
      calc 2 / (3 * π ^ 2) * min 1 (y ^ 2)
          ≤ 2 / (3 * π ^ 2) * y ^ 2 := mul_le_mul_of_nonneg_left (min_le_right _ _) hcpos
        _ ≤ 1 - Real.sinc y := hkey
    · have hy2 : 1 ≤ y ^ 2 := by nlinarith [Real.pi_gt_three, hyπ]
      rw [min_eq_left hy2, mul_one]
      have hsinc_le : Real.sinc y ≤ y⁻¹ := by
        have := Real.sinc_le_inv_abs hypos.ne'
        rwa [abs_of_pos hypos] at this
      have hinv : y⁻¹ ≤ π⁻¹ := inv_anti₀ Real.pi_pos hyπ.le
      calc 2 / (3 * π ^ 2) ≤ 1 - π⁻¹ := leanlevy_chat20_sinc_lower_const
        _ ≤ 1 - y⁻¹ := by linarith
        _ ≤ 1 - Real.sinc y := by linarith
