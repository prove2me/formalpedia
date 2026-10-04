-- Prove2me | solution 1 for ZetaNine.CoefficientMapJet.integer_coefficient_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-03T16:17:26.103419+00:00
-- url     : https://prove2.me/submissions/32bc23d9-001c-4a69-89e8-9a45984f2567

import Definitions.Def_ZetaNine_CoefficientMapJet
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal

open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMap

theorem clearedPoleProduct_ne_zero (n j : ℕ) :
    clearedPoleProduct n j (-(j : ℚ)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hkj := (Finset.mem_erase.mp hk).1
  intro hz
  have he : (k : ℚ) = (j : ℚ) := by linarith
  exact hkj (Nat.cast_inj.mp he)

end ZetaNine.CoefficientMap



/-!
Actual local formal jets of the p=9, q=1, m=n rational function.
The coefficients are extracted from the genuine shifted numerator divided
by the genuine cleared denominator, in formal power series with nonzero
constant denominator. They are not abstract coefficient inputs.

This proves the all-order local multiplier convolution, not a global
partial-fraction decomposition, the full five-dimensional map or its inverse.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapJet




















theorem shiftedVariable_eval (j : ℕ) (z : ℚ) :
    (shiftedVariable j).eval z = -(j : ℚ) + z := by
  simp [shiftedVariable]
  ring

theorem shiftedNumerator_eval (n j : ℕ) (z : ℚ) :
    (shiftedNumerator n j).eval z = ZetaNine.CoefficientMap.numerator n (-(j : ℚ) + z) := by
  simp only [shiftedNumerator, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_add, shiftedVariable_eval]
  rfl

theorem shiftedClearedDenominator_eval (n j : ℕ) (z : ℚ) :
    (shiftedClearedDenominator n j).eval z = ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ) + z) := by
  simp only [shiftedClearedDenominator, Polynomial.eval_prod, Polynomial.eval_add,
    Polynomial.eval_C, shiftedVariable_eval]
  rfl

theorem actual_local_rational_expression (n j : ℕ) (z : ℚ) :
    (shiftedNumerator n j).eval z / (shiftedClearedDenominator n j).eval z ^ 9 =
      ZetaNine.CoefficientMap.clearedR n j (-(j : ℚ) + z) := by
  rw [shiftedNumerator_eval, shiftedClearedDenominator_eval]
  rfl

theorem localU_eval (n j : ℕ) (z : ℚ) :
    (localU n j).eval z = (-(j : ℚ) + z) * (-(j : ℚ) + z + n) := by
  simp [localU, shiftedVariable_eval]

theorem localU_eq (n j : ℕ) (hj : j ≤ n) :
    localU n j = C (-(j : ℚ) * (n - j : ℕ)) +
      C ((n : ℚ) - 2 * j) * X + X ^ 2 := by
  simp only [localU, shiftedVariable, Nat.cast_sub hj, map_mul, map_sub, map_neg, map_ofNat]
  ring

theorem integerLocalU_map (n j : ℕ) (hj : j ≤ n) :
    (integerLocalU n j).map (Int.castRingHom ℚ) = localU n j := by
  rw [localU_eq n j hj]
  simp [integerLocalU, map_ofNat]

theorem actual_weighted_local_rational_expression (n j : ℕ) (W : ℚ[X]) (z : ℚ) :
    (shiftedNumerator n j * W.comp (localU n j)).eval z /
        (shiftedClearedDenominator n j).eval z ^ 9 =
      ZetaNine.CoefficientMap.clearedWeightedR n j W (-(j : ℚ) + z) := by
  rw [Polynomial.eval_mul, Polynomial.eval_comp, shiftedNumerator_eval,
    shiftedClearedDenominator_eval, localU_eval]
  unfold ZetaNine.CoefficientMap.clearedWeightedR ZetaNine.CoefficientMap.clearedR
  simp only [div_eq_mul_inv]
  ring

theorem shiftedClearedDenominator_constant (n j : ℕ) :
    PowerSeries.constantCoeff (shiftedClearedDenominator n j : PowerSeries ℚ) =
      ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ)) := by
  rw [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    shiftedClearedDenominator_eval]
  simp

theorem shiftedClearedDenominator_constant_ne_zero (n j : ℕ) :
    PowerSeries.constantCoeff (shiftedClearedDenominator n j : PowerSeries ℚ) ≠ 0 := by
  rw [shiftedClearedDenominator_constant]
  exact ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero n j

theorem clearedSeries_denominator_identity (n j : ℕ) :
    clearedSeries n j * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j : PowerSeries ℚ) := by
  have h : PowerSeries.constantCoeff ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (shiftedClearedDenominator_constant_ne_zero n j)
  unfold clearedSeries
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

theorem clearedSeries_unique (n j : ℕ) (S : PowerSeries ℚ)
    (hS : S * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j : PowerSeries ℚ)) : S = clearedSeries n j := by
  have h : PowerSeries.constantCoeff ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ (shiftedClearedDenominator_constant_ne_zero n j)
  unfold clearedSeries
  calc
    S = S * ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 *
        ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹) := by
      rw [PowerSeries.mul_inv_cancel _ h, mul_one]
    _ = (S * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9) *
        ((shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9)⁻¹ := (mul_assoc _ _ _).symm
    _ = _ := by rw [hS]

theorem weightedClearedSeries_denominator_identity (n j : ℕ) (W : ℚ[X]) :
    weightedClearedSeries n j W * (shiftedClearedDenominator n j : PowerSeries ℚ) ^ 9 =
      (shiftedNumerator n j * W.comp (localU n j) : ℚ[X]) := by
  unfold weightedClearedSeries
  rw [mul_right_comm, clearedSeries_denominator_identity, Polynomial.coe_mul]

theorem clearedSeries_constant (n j : ℕ) :
    PowerSeries.constantCoeff (clearedSeries n j) = ZetaNine.CoefficientMap.leadingPoleCoefficient n j := by
  simp only [clearedSeries, map_mul, PowerSeries.constantCoeff_inv, map_pow,
    Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    shiftedNumerator_eval, shiftedClearedDenominator_eval, add_zero]
  rfl

theorem localCoefficient_nine (n j : ℕ) :
    localCoefficient n j 9 = ZetaNine.CoefficientMap.leadingPoleCoefficient n j := by
  simp only [localCoefficient, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact clearedSeries_constant n j

theorem weightedLocalCoefficient_nine (n j : ℕ) (W : ℚ[X]) :
    weightedLocalCoefficient n j 9 W = ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient n j W := by
  simp only [weightedLocalCoefficient, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, weightedClearedSeries, map_mul,
    clearedSeries_constant, Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp, localU_eval, add_zero]
  rfl

theorem coefficient_convolution (n j s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℚ[X]) :
    weightedLocalCoefficient n j s W =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l * (W.comp (localU n j)).coeff (l - s) := by
  unfold weightedLocalCoefficient weightedClearedSeries
  rw [PowerSeries.coeff_mul]
  simp only [Polynomial.coeff_coe]
  apply Finset.sum_nbij' (fun d : ℕ × ℕ => 9 - d.1) (fun l : ℕ => (9 - l, l - s))
  · intro d hd
    have hd' := Finset.mem_antidiagonal.mp hd
    rw [Finset.mem_Icc]
    omega
  · intro l hl
    have hl' := Finset.mem_Icc.mp hl
    rw [Finset.mem_antidiagonal]
    omega
  · intro d hd
    have hd' := Finset.mem_antidiagonal.mp hd
    apply Prod.ext <;> dsimp <;> omega
  · intro l hl
    have hl' := Finset.mem_Icc.mp hl
    omega
  · intro d hd
    have hd' := Finset.mem_antidiagonal.mp hd
    unfold localCoefficient
    have hfirst : 9 - (9 - d.1) = d.1 := by omega
    have hsecond : 9 - d.1 - s = d.2 := by omega
    rw [hfirst, hsecond]

theorem coefficient_convolution_explicit (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℚ[X]) :
    weightedLocalCoefficient n j s W =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        (W.comp (C (-(j : ℚ) * (n - j : ℕ)) +
          C ((n : ℚ) - 2 * j) * X + X ^ 2)).coeff (l - s) := by
  rw [coefficient_convolution n j s hs1 hs9 W, localU_eq n j hj]

theorem checked_integer_coefficient_convolution (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℤ[X]) :
    weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ)) =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        ((W.comp (integerLocalU n j)).coeff (l - s) : ℚ) := by
  rw [coefficient_convolution n j s hs1 hs9]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← integerLocalU_map n j hj, ← Polynomial.map_comp]
  simp

end ZetaNine.CoefficientMapJet













open ZetaNine.CoefficientMapJet

theorem solution (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℤ[X]) :
    weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ)) =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        ((W.comp (integerLocalU n j)).coeff (l - s) : ℚ) := by
  exact ZetaNine.CoefficientMapJet.checked_integer_coefficient_convolution n j s hj hs1 hs9 W

#print axioms solution
