-- Prove2me | solution 1 for UpperTheory.sum_log_primeFactors_mul_two_add_logb_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:03:55.32694+00:00
-- url     : https://prove2.me/submissions/950ac64c-2452-4289-823a-5606339f1295

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_CMTraceForms_SumLogPrimeFactorsMulTwoAddLogbLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ (Q : ℕ) (y : ℝ), Q ≠ 0 → 1 ≤ y → Real.log Q ≤ y →
      (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) * (2 + Real.logb 2 Q) ≤ 11 * y ^ 4 := by
  intro Q y hQ hy hlog
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hpos : ∀ p ∈ Q.primeFactors, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have h1 : (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) ≤ y := by
    rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
    refine le_trans (Real.log_le_log (Finset.prod_pos hpos) ?_) hlog
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) (Nat.prod_primeFactors_dvd Q)
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr this
  have h2 : Real.logb 2 Q ≤ 2 * y := by
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : 0 ≤ Real.logb 2 Q := Real.logb_nonneg (by norm_num) hQ1
  have h4 : y ^ 2 ≤ y ^ 4 := pow_le_pow_right₀ hy (by norm_num)
  calc (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) * (2 + Real.logb 2 Q)
      ≤ y * (2 + Real.logb 2 Q) := mul_le_mul_of_nonneg_right h1 (by linarith)
    _ ≤ y * (4 * y) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ 11 * y ^ 4 := by nlinarith
end UpperTheory
