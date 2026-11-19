-- Prove2me | solution 1 for PowerSeries.katz_positive_coefficient_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-18T15:58:56.287881+00:00
-- url     : https://prove2.me/submissions/bda6d881-3836-44c0-8769-c4e76270b4f9

import Mathlib

set_option autoImplicit false

namespace UploadRankinPosCoef

open PowerSeries Finset.HasAntidiagonal

/-- The coefficient recursion of `Y' = Y · A`: `Y_(n+1) (n+1) = Σ_(i+j=n) Y_i A_j`. -/
theorem coeff_succ_of_deriv {Y A : PowerSeries ℝ} (h : derivative ℝ Y = Y * A) (n : ℕ) :
    coeff (n + 1) Y * (n + 1) = ∑ p ∈ antidiagonal n, coeff p.1 Y * coeff p.2 A := by
  rw [← coeff_derivative, h, coeff_mul]

theorem natCast_add_one_pos' (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by
  have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact add_pos_of_nonneg_of_pos h1 zero_lt_one

theorem inv_natCast_add_one_nonneg (n : ℕ) : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity

theorem eq_mul_inv_natCast (a : ℝ) (n : ℕ) : a = a * ((n : ℝ) + 1) * ((n : ℝ) + 1)⁻¹ := by
  rw [mul_assoc, mul_inv_cancel₀ (natCast_add_one_pos' n).ne', mul_one]

theorem le_of_mul_natCast_le {a b : ℝ} {n : ℕ} (h : a * ((n : ℝ) + 1) ≤ b * ((n : ℝ) + 1)) : a ≤ b := by
  rw [eq_mul_inv_natCast a n, eq_mul_inv_natCast b n]
  exact mul_le_mul_of_nonneg_right h (inv_natCast_add_one_nonneg n)

/-- Positive Coefficient Lemma, part 1: `Y(0) = 1`, `Y' = Y A`, `A ≥ 0` coefficientwise imply `Y ≥ 0`. -/
theorem posCoef_nonneg {Y A : PowerSeries ℝ} (h0 : constantCoeff Y = 1) (h : derivative ℝ Y = Y * A)
    (hA : ∀ j, 0 ≤ coeff j A) : ∀ n, 0 ≤ coeff n Y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply, h0]; exact zero_le_one
    | succ n =>
      have key := coeff_succ_of_deriv h n
      have hs : 0 ≤ ∑ p ∈ antidiagonal n, coeff p.1 Y * coeff p.2 A := by
        refine Finset.sum_nonneg fun p hp => mul_nonneg (ih p.1 ?_) (hA _)
        have := mem_antidiagonal.mp hp
        omega
      rw [← key, ← zero_mul ((n : ℝ) + 1)] at hs
      exact le_of_mul_natCast_le hs

/-- Positive Coefficient Lemma, part 2: with `Z(0) = 1`, `Z' = Z B`, `0 ≤ B ≤ A` coefficientwise, `Z ≤ Y`. -/
theorem posCoef_le {Y Z A B : PowerSeries ℝ} (hY0 : constantCoeff Y = 1) (hZ0 : constantCoeff Z = 1)
    (hY : derivative ℝ Y = Y * A) (hZ : derivative ℝ Z = Z * B) (hB : ∀ j, 0 ≤ coeff j B)
    (hBA : ∀ j, coeff j B ≤ coeff j A) : ∀ n, coeff n Z ≤ coeff n Y := by
  have hZn := posCoef_nonneg hZ0 hZ hB
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, hY0, hZ0]
    | succ n =>
      have kY := coeff_succ_of_deriv hY n
      have kZ := coeff_succ_of_deriv hZ n
      have hs : ∑ p ∈ antidiagonal n, coeff p.1 Z * coeff p.2 B ≤
          ∑ p ∈ antidiagonal n, coeff p.1 Y * coeff p.2 A := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp' := mem_antidiagonal.mp hp
        have h1 := ih p.1 (by omega)
        exact mul_le_mul h1 (hBA _) (hB _) (le_trans (hZn _) h1)
      rw [← kY, ← kZ] at hs
      exact le_of_mul_natCast_le hs

theorem main (Y Z A B : PowerSeries ℝ)
    (hY0 : PowerSeries.constantCoeff Y = 1) (hZ0 : PowerSeries.constantCoeff Z = 1)
    (hY : PowerSeries.derivative ℝ Y = Y * A) (hZ : PowerSeries.derivative ℝ Z = Z * B)
    (hB : ∀ j : ℕ, 0 ≤ PowerSeries.coeff j B)
    (hBA : ∀ j : ℕ, PowerSeries.coeff j B ≤ PowerSeries.coeff j A) (n : ℕ) :
    0 ≤ PowerSeries.coeff n Z ∧ PowerSeries.coeff n Z ≤ PowerSeries.coeff n Y :=
  ⟨posCoef_nonneg hZ0 hZ hB n, posCoef_le hY0 hZ0 hY hZ hB hBA n⟩

end UploadRankinPosCoef

theorem solution (Y Z A B : PowerSeries ℝ)
    (hY0 : PowerSeries.constantCoeff Y = 1) (hZ0 : PowerSeries.constantCoeff Z = 1)
    (hY : PowerSeries.derivative ℝ Y = Y * A) (hZ : PowerSeries.derivative ℝ Z = Z * B)
    (hB : ∀ j : ℕ, 0 ≤ PowerSeries.coeff j B)
    (hBA : ∀ j : ℕ, PowerSeries.coeff j B ≤ PowerSeries.coeff j A) (n : ℕ) :
    0 ≤ PowerSeries.coeff n Z ∧ PowerSeries.coeff n Z ≤ PowerSeries.coeff n Y := by
  exact UploadRankinPosCoef.main Y Z A B hY0 hZ0 hY hZ hB hBA n
