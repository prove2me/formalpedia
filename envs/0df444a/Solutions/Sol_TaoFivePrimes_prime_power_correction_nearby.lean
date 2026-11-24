-- Prove2me | solution 1 for TaoFivePrimes.prime_power_correction_nearby
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T18:48:22.81441+00:00
-- url     : https://prove2.me/submissions/d178d4c9-f10e-43dd-934f-c2305e583635

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_psi_le
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large

/-!
# Prime-power correction in a short interval

The completed unconditional Chebyshev estimate, combined with the
Costa--Pereira inequalities in Mathlib, controls the difference of psi-theta
at nearby large arguments. No short-prime-interval theorem is used.
-/

namespace ShortPrimeIntervalPrimePowers

theorem cubert_le_sqrt_div_1000 (x : ℝ) (hx : (10 : ℝ)^18 ≤ x) :
    x ^ (3 : ℝ)⁻¹ ≤ Real.sqrt x / 1000 := by
  have hx0 : 0 < x := by norm_num at hx; linarith
  have hlow : (1000 : ℝ) ≤ x ^ (6 : ℝ)⁻¹ := by
    calc
      1000 = ((1000 : ℝ)^6) ^ (6 : ℝ)⁻¹ :=
        (Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 1000) (by norm_num : (6 : ℕ) ≠ 0)).symm
      _ ≤ x ^ (6 : ℝ)⁻¹ := Real.rpow_le_rpow (by positivity)
        (by norm_num at hx ⊢; exact hx) (by norm_num)
  have hprod : x ^ (3 : ℝ)⁻¹ * x ^ (6 : ℝ)⁻¹ = Real.sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hmul := mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg hx0.le ((3 : ℝ)⁻¹))
  rw [hprod] at hmul
  linarith

theorem sqrt_psi_error (x : ℝ) (hx : (10 : ℝ)^18 ≤ x) :
    |Chebyshev.psi (Real.sqrt x) - Real.sqrt x| ≤ Real.sqrt x / 80 := by
  have hx0 : 0 < x := by norm_num at hx; linarith
  have hr : (10 : ℝ)^9 ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    norm_num at hx ⊢
    exact hx
  have hr0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have he2 : Real.exp 2 ≤ (9 : ℝ) := by
    have he : Real.exp 1 ≤ (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
    have hp := pow_le_pow_left₀ (Real.exp_pos 1).le he 2
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    exact hp
  have hl : (2 : ℝ) ≤ Real.log (Real.sqrt x) :=
    (Real.le_log_iff_exp_le hr0).mpr (he2.trans (by norm_num at hr ⊢; linarith))
  exact (TaoFivePrimes.schoenfeld_psi_error_large (Real.sqrt x)
    (by norm_num at hr ⊢; linarith)).trans
    (div_le_div_of_nonneg_left hr0.le (by norm_num) (by linarith))

theorem prime_power_bounds (x : ℝ) (hx : (10 : ℝ)^18 ≤ x) :
    (79/80 : ℝ) * Real.sqrt x ≤ Chebyshev.psi x - Chebyshev.theta x ∧
      Chebyshev.psi x - Chebyshev.theta x ≤ (203/200 : ℝ) * Real.sqrt x := by
  have hx0 : 0 < x := by norm_num at hx; linarith
  have hx1 : 1 ≤ x := by norm_num at hx; linarith
  have hc := cubert_le_sqrt_div_1000 x hx
  have hf : x ^ (5 : ℝ)⁻¹ ≤ x ^ (3 : ℝ)⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hpsi3 := TaoFivePrimes.rosser_schoenfeld_psi_le (x ^ (3 : ℝ)⁻¹) (by positivity)
  have hpsi5 := TaoFivePrimes.rosser_schoenfeld_psi_le (x ^ (5 : ℝ)⁻¹) (by positivity)
  have he := abs_le.mp (sqrt_psi_error x hx)
  have hlow := Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi hx0.le
  have hupp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hs : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
    simpa only [one_div] using (Real.sqrt_eq_rpow x).symm
  rw [hs] at hlow hupp
  have hnon3 := Chebyshev.psi_nonneg (x ^ (3 : ℝ)⁻¹)
  have hnon7 := Chebyshev.psi_nonneg (x ^ (7 : ℝ)⁻¹)
  constructor
  · nlinarith only [hlow, he.1, hnon3, hnon7]
  · nlinarith only [hupp, he.2, hpsi3, hpsi5, hc, hf, Real.sqrt_nonneg x]

/-- The source paper's 0.0325 square-root correction follows from the already
completed Chebyshev branch, with room in the constants. -/
theorem nearby_prime_power_correction (x y : ℝ) (hx : (10 : ℝ)^18 ≤ x)
    (hxy : x ≤ y) (hroot : Real.sqrt y ≤ (10001/10000 : ℝ) * Real.sqrt x) :
    (Chebyshev.psi y - Chebyshev.theta y) -
      (Chebyshev.psi x - Chebyshev.theta x) ≤ (13/400 : ℝ) * Real.sqrt x := by
  have hxlo := (prime_power_bounds x hx).1
  have hyhi := (prime_power_bounds y (hx.trans hxy)).2
  nlinarith only [hxlo, hyhi, hroot, Real.sqrt_nonneg x]

end ShortPrimeIntervalPrimePowers

theorem solution (x y : ℝ) (hx : (10 : ℝ)^18 ≤ x) (hxy : x ≤ y)
    (hroot : Real.sqrt y ≤ (10001/10000 : ℝ) * Real.sqrt x) :
    (Chebyshev.psi y - Chebyshev.theta y) -
      (Chebyshev.psi x - Chebyshev.theta x) ≤ (13/400 : ℝ) * Real.sqrt x :=
  ShortPrimeIntervalPrimePowers.nearby_prime_power_correction x y hx hxy hroot
