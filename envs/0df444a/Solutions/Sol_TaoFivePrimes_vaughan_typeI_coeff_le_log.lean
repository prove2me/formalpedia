-- Prove2me | solution 1 for TaoFivePrimes.vaughan_typeI_coeff_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-13T16:22:54.243641+00:00
-- url     : https://prove2.me/submissions/4f2ca221-fa25-4e45-aaee-ce212212fbe6

import Mathlib
import Definitions.Def_TaoFivePrimes_VaughanTruncation

open TaoFivePrimes

theorem solution (U V : ℝ) (d : ℕ) :
    |(truncLe U moebiusR * truncLe V ArithmeticFunction.vonMangoldt) d| ≤ Real.log d := by
  rw [ArithmeticFunction.mul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ p ∈ d.divisorsAntidiagonal,
      |truncLe U moebiusR p.1 * truncLe V ArithmeticFunction.vonMangoldt p.2|
        ≤ ArithmeticFunction.vonMangoldt p.2 := by
    rintro ⟨a, b⟩ hp
    have hmu : |truncLe U moebiusR a| ≤ 1 := by
      rw [truncLe_apply]
      split
      · have h0 : |(ArithmeticFunction.moebius a : ℤ)| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
        have h1 : |((ArithmeticFunction.moebius a : ℤ) : ℝ)| ≤ 1 := by exact_mod_cast h0
        simpa using h1
      · norm_num
    have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt b := ArithmeticFunction.vonMangoldt_nonneg
    have hvm : |truncLe V ArithmeticFunction.vonMangoldt b|
        ≤ ArithmeticFunction.vonMangoldt b := by
      rw [truncLe_apply]
      split
      · exact le_of_eq (abs_of_nonneg hvm0)
      · simpa using hvm0
    calc |truncLe U moebiusR a * truncLe V ArithmeticFunction.vonMangoldt b|
        = |truncLe U moebiusR a| * |truncLe V ArithmeticFunction.vonMangoldt b| := abs_mul _ _
      _ ≤ 1 * ArithmeticFunction.vonMangoldt b :=
          mul_le_mul hmu hvm (abs_nonneg _) (by norm_num)
      _ = ArithmeticFunction.vonMangoldt b := one_mul _
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hz : (zetaR * ArithmeticFunction.vonMangoldt) d = Real.log d := by
      rw [ArithmeticFunction.zeta_mul_vonMangoldt, ArithmeticFunction.log_apply]
    rw [ArithmeticFunction.mul_apply] at hz
    have hcong : ∑ p ∈ d.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt p.2
        = ∑ p ∈ d.divisorsAntidiagonal, zetaR p.1 * ArithmeticFunction.vonMangoldt p.2 := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      have hmem := Nat.mem_divisorsAntidiagonal.mp hp
      have hp1 : p.1 ≠ 0 := by
        rintro h
        rw [h, zero_mul] at hmem
        exact hmem.2 hmem.1.symm
      have hzp : zetaR p.1 = 1 := by
        simp [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, hp1]
      rw [hzp, one_mul]
    rw [hcong, hz]
