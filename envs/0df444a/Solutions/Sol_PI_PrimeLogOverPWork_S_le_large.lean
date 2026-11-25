-- Prove2me | solution 1 for PI.PrimeLogOverPWork.S_le_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:27.188797+00:00
-- url     : https://prove2.me/submissions/77ba1013-cd30-4458-b438-a93287df7d77

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork
import Theorems.Thm_PI_PrimeLogOverPWork_log_factorial_ge
import Theorems.Thm_PI_PrimeLogOverPWork_le_log_of_pow_le
import Theorems.Thm_PI_PrimeLogOverPWork_log_factorial_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
private theorem theta_eq_sum_log_primes (n : ℕ) :
    Chebyshev.theta n = ∑ p ∈ Ioc 0 n with p.Prime, Real.log p := by
  simp [Chebyshev.theta]
private theorem theta_le_two_mul_log_two (n : ℕ) : Chebyshev.theta n ≤ 2 * n * Real.log 2 := by
  have hset : ({p ∈ Ioc 0 n | p.Prime} : Finset ℕ) = {p ∈ range (n + 1) | p.Prime} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, h⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨h, hp⟩
      exact ⟨⟨hp.pos, by omega⟩, hp⟩
  have hprod : ∑ p ∈ Ioc 0 n with p.Prime, Real.log p = Real.log (primorial n : ℝ) := by
    rw [hset, primorial, Nat.cast_prod, Real.log_prod]
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  rw [theta_eq_sum_log_primes, hprod]
  have h4 : (primorial n : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast primorial_le_four_pow n
  have hpos : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  calc Real.log (primorial n : ℝ) ≤ Real.log ((4 : ℝ) ^ n) := Real.log_le_log hpos h4
    _ = 2 * n * Real.log 2 := by
      rw [Real.log_pow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
end PI.PrimeLogOverPWork
end

set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
namespace PI.PrimeLogOverPWork
theorem _root_.solution (n : ℕ) (hn : 64 ≤ n) : S n ≤ Real.log (n : ℝ) := by
  have hn' : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h1 := log_factorial_ge n (by omega)
  have h2 := log_factorial_le n (by omega)
  have hθ := theta_le_two_mul_log_two n
  have hL1 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL0 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have h3 : (19 : ℝ) / 12 * Real.log 2 ≤ Real.log 3 := by
    have := le_log_of_pow_le 3 19 12 (by norm_num) (by norm_num)
    simpa using this
  have h5 : (51 : ℝ) / 22 * Real.log 2 ≤ Real.log 5 := by
    have := le_log_of_pow_le 5 51 22 (by norm_num) (by norm_num)
    simpa using this
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  have hlogn : Real.log n ≤ n / 64 - 1 + 6 * Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hnpos (by norm_num : (0 : ℝ) < 64))
    rw [Real.log_div hnpos.ne' (by norm_num)] at h
    linarith
  have hnL : (n : ℝ) * Real.log 2 ≤ n * 0.6931471808 := mul_le_mul_of_nonneg_left hL1.le hnpos.le
  have h3' : (19 : ℝ) / 12 * Real.log 2 * ((n : ℝ) * (4 / 27) - 2)
      ≤ Real.log 3 * ((n : ℝ) * (4 / 27) - 2) := mul_le_mul_of_nonneg_right h3 (by linarith)
  have h5' : (51 : ℝ) / 22 * Real.log 2 * ((n : ℝ) / 25 - 1)
      ≤ Real.log 5 * ((n : ℝ) / 25 - 1) := mul_le_mul_of_nonneg_right h5 (by linarith)
  have key : (n : ℝ) * S n ≤ n * Real.log n := by linarith
  exact le_of_mul_le_mul_left key hnpos
end PI.PrimeLogOverPWork
