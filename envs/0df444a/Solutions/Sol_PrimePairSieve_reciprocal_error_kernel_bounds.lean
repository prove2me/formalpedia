-- Prove2me | solution 1 for PrimePairSieve.reciprocal_error_kernel_bounds
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T11:45:13.076314+00:00
-- url     : https://prove2.me/submissions/83c7783f-474d-4339-b8df-6e5de1c43803

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic

open Real MeasureTheory Set
open scoped BigOperators

noncomputable section
set_option autoImplicit false

private lemma power_integrable (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ ((n : ℝ) - 1 / 3)) (Ioc 0 1) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
  apply intervalIntegral.intervalIntegrable_rpow'
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

private lemma power_integral (n : ℕ) :
    (∫ x in Ioc (0 : ℝ) 1, x ^ ((n : ℝ) - 1 / 3)) = 1 / ((n : ℝ) + 2 / 3) := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by have := Nat.cast_nonneg (α := ℝ) n; linarith))]
  have hp : 0 < (n : ℝ) - 1 / 3 + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [Real.one_rpow, Real.zero_rpow hp.ne', sub_zero]
  congr 1
  ring

private def lowerCoeff : Fin 6 → ℝ := ![1, -2, 77/27, -317/108, 49/27, -13/27]
private def upperCoeff : Fin 5 → ℝ := ![1, -203/108, 115/54, -37/27, 10/27]

private def weightedPoly {m : ℕ} (c : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ n : Fin m, c n * x ^ (((n : ℕ) : ℝ) - 1 / 3)

private def poly {m : ℕ} (c : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ n : Fin m, c n * x ^ (n : ℕ)

private lemma weightedPoly_eq {m : ℕ} (c : Fin m → ℝ) {x : ℝ} (hx : 0 < x) :
    weightedPoly c x = x ^ (-(1 / 3 : ℝ)) * poly c x := by
  unfold weightedPoly poly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hp : x ^ (((n : ℕ) : ℝ) - 1 / 3) = x ^ (n : ℕ) * x ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]
    congr 1
  rw [hp]
  ring

private lemma weightedPoly_integrable {m : ℕ} (c : Fin m → ℝ) :
    IntegrableOn (weightedPoly c) (Ioc (0 : ℝ) 1) := by
  unfold weightedPoly
  apply integrable_finsetSum
  intro n _
  exact (power_integrable (n : ℕ)).const_mul _

private lemma weightedPoly_integral {m : ℕ} (c : Fin m → ℝ) :
    (∫ x in Ioc (0 : ℝ) 1, weightedPoly c x) =
      ∑ n : Fin m, c n / (((n : ℕ) : ℝ) + 2 / 3) := by
  unfold weightedPoly
  rw [integral_finsetSum (Finset.univ : Finset (Fin m)) (fun n _ => (power_integrable (n : ℕ)).const_mul (c n))]
  simp_rw [integral_const_mul, power_integral, mul_one_div]

private lemma lower_poly_le {x : ℝ} (hx : 0 ≤ x) :
    poly lowerCoeff x ≤ 1 / (1 + x) ^ 2 := by
  have hid : 1 - (1 + x) ^ 2 * poly lowerCoeff x =
      x ^ 2 * (1 - x) ^ 2 * (2 * x - 1) ^ 2 * (4 / 27 + 13 / 108 * x) := by
    norm_num [poly, lowerCoeff, Fin.sum_univ_succ]
    ring
  have h : 0 ≤ 1 - (1 + x) ^ 2 * poly lowerCoeff x := by
    rw [hid]
    positivity
  apply (le_div_iff₀ (by positivity : 0 < (1 + x) ^ 2)).mpr
  simpa [mul_comm] using sub_nonneg.mp h

private lemma upper_poly_ge {x : ℝ} (hx : 0 ≤ x) :
    1 / (1 + x) ^ 2 ≤ poly upperCoeff x := by
  have hid : (1 + x) ^ 2 * poly upperCoeff x - 1 =
      x * (1 - x) ^ 2 * (2 * x - 1) ^ 2 * (13 / 108 + 5 / 54 * x) := by
    norm_num [poly, upperCoeff, Fin.sum_univ_succ]
    ring
  have h : 0 ≤ (1 + x) ^ 2 * poly upperCoeff x - 1 := by
    rw [hid]
    positivity
  apply (div_le_iff₀ (by positivity : 0 < (1 + x) ^ 2)).mpr
  simpa [mul_comm] using sub_nonneg.mp h

private lemma kernel_integrable :
    IntegrableOn (fun x : ℝ => x ^ (-(1 / 3 : ℝ)) / (1 + x) ^ 2) (Ioc 0 1) := by
  have hp : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 3 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hc : ContinuousOn (fun x : ℝ => 1 / (1 + x) ^ 2) (uIcc 0 1) := by
    apply continuousOn_const.div ((continuousOn_const.add continuousOn_id).pow 2)
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1] : 0 < 1 + x))
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
  simpa only [mul_one_div] using hp.mul_continuousOn hc

theorem solution :
    (6529 / 7480 : ℝ) ≤ (∫ x in Ioc (0 : ℝ) 1, x ^ (-(1 / 3 : ℝ)) / (1 + x) ^ 2) ∧
    (∫ x in Ioc (0 : ℝ) 1, x ^ (-(1 / 3 : ℝ)) / (1 + x) ^ 2) ≤ (5399 / 6160 : ℝ) := by
  have hlint : (∫ x in Ioc (0 : ℝ) 1, weightedPoly lowerCoeff x) = 6529 / 7480 := by
    rw [weightedPoly_integral]
    norm_num [lowerCoeff, Fin.sum_univ_succ]
  have huint : (∫ x in Ioc (0 : ℝ) 1, weightedPoly upperCoeff x) = 5399 / 6160 := by
    rw [weightedPoly_integral]
    norm_num [upperCoeff, Fin.sum_univ_succ]
  constructor
  · rw [← hlint]
    apply integral_mono_ae (weightedPoly_integrable lowerCoeff) kernel_integrable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [weightedPoly_eq lowerCoeff hx.1]
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left (lower_poly_le hx.1.le) (Real.rpow_nonneg hx.1.le (-(1 / 3 : ℝ)))
  · rw [← huint]
    apply integral_mono_ae kernel_integrable (weightedPoly_integrable upperCoeff)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [weightedPoly_eq upperCoeff hx.1]
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left (upper_poly_ge hx.1.le) (Real.rpow_nonneg hx.1.le (-(1 / 3 : ℝ)))

#print axioms solution
