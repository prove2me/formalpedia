-- Prove2me | solution 1 for TaoFivePrimes.theorem51_sharp_transfer_gap_global_cancellation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-29T20:42:35.053849+00:00
-- url     : https://prove2.me/submissions/ee9fcacb-712c-4822-a14f-1d6d7b417756
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_theorem51_pure_moebius_transfer_bound

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace TaoFivePrimes

private lemma arithmeticRestrictLE_apply (B : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    arithmeticRestrictLE B f n = if n ≤ B then f n else 0 := rfl

-- The coefficient estimate follows from |μ| ≤ 1 and ζ * Λ = log.
private lemma correctionCoefficient_abs_le_log (U V : ℝ) (d : ℕ) :
    |vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d| ≤ Real.log d := by
  rw [vaughanTypeICorrectionCoefficient, ArithmeticFunction.mul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ d.divisorsAntidiagonal,
      |arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) p.1 *
          arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt p.2|
        ≤ ArithmeticFunction.vonMangoldt p.2 := by
    rintro ⟨a, b⟩ _hp
    have hmu : |arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) a| ≤ 1 := by
      have h0 : |(ArithmeticFunction.moebius a : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
      have h1 : |((ArithmeticFunction.moebius a : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h0
      rw [arithmeticRestrictLE_apply]
      split
      · simpa using h1
      · norm_num
    have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt b := ArithmeticFunction.vonMangoldt_nonneg
    have hvm : |arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt b|
        ≤ ArithmeticFunction.vonMangoldt b := by
      rw [arithmeticRestrictLE_apply]
      split
      · exact le_of_eq (abs_of_nonneg hvm0)
      · simpa using hvm0
    calc |arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) a *
            arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt b|
        = |arithmeticRestrictLE ⌊U⌋₊ (μ : ArithmeticFunction ℝ) a| *
            |arithmeticRestrictLE ⌊V⌋₊ ArithmeticFunction.vonMangoldt b| := abs_mul _ _
      _ ≤ 1 * ArithmeticFunction.vonMangoldt b :=
          mul_le_mul hmu hvm (abs_nonneg _) (by norm_num)
      _ = ArithmeticFunction.vonMangoldt b := one_mul _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hz : (ArithmeticFunction.zeta * ArithmeticFunction.vonMangoldt) d = Real.log d := by
      rw [ArithmeticFunction.zeta_mul_vonMangoldt, ArithmeticFunction.log_apply]
    rw [ArithmeticFunction.mul_apply] at hz
    have hz' : ∑ p ∈ d.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt p.2 = Real.log d := by
      rw [← hz]
      apply Finset.sum_congr rfl
      intro p hp
      have hp0 : p.1 ≠ 0 := by
        intro h0
        have h1 := (Nat.mem_divisorsAntidiagonal.mp hp).1
        rw [h0, zero_mul] at h1
        omega
      simp [ArithmeticFunction.zeta_apply, hp0]
    exact le_of_eq hz'

end TaoFivePrimes

theorem solution
    (x alpha U V : ℝ) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUx : U < x) (hVx : V < x)
    (hUVx : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ‖TaoFivePrimes.typeISlabS3 x alpha U V‖ ≤
      ∑ d ∈ TaoFivePrimes.theorem51Divisors U V,
        ((1 - ‖(if d ≤ ⌊U⌋₊ then (ArithmeticFunction.moebius d : ℂ) else 0)‖) *
            ‖TaoFivePrimes.typeISlabS1 x alpha d‖
          + (Real.log d -
              ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖) *
              ‖TaoFivePrimes.typeISlabS0 x alpha d‖) := by
  have hcore :=
    TaoFivePrimes.theorem51_pure_moebius_transfer_bound
      x alpha U V hU hV hUx hVx hUVx hUV2
  apply hcore.trans
  apply Finset.sum_le_sum
  intro d hd
  have hcoeff :
      ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖
        ≤ Real.log d := by
    rw [Complex.norm_real]
    exact TaoFivePrimes.correctionCoefficient_abs_le_log U V d
  have hterm :
      0 ≤ (Real.log d -
          ‖(((TaoFivePrimes.vaughanTypeICorrectionCoefficient ⌊U⌋₊ ⌊V⌋₊ d : ℝ) : ℂ))‖) *
          ‖TaoFivePrimes.typeISlabS0 x alpha d‖ :=
    mul_nonneg (sub_nonneg.mpr hcoeff) (norm_nonneg _)
  exact le_add_of_nonneg_right hterm
