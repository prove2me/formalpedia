-- Prove2me | solution 1 for PI.PrimeLogOverPWork.sum_E_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:03.948816+00:00
-- url     : https://prove2.me/submissions/04b7dfa8-b84a-41b8-bc21-950230c17c0f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_PrimeLogOverPWork
import Theorems.Thm_PI_PrimeLogOverPWork_vm4
import Theorems.Thm_PI_PrimeLogOverPWork_vm8
import Theorems.Thm_PI_PrimeLogOverPWork_vm16
import Theorems.Thm_PI_PrimeLogOverPWork_vm9
import Theorems.Thm_PI_PrimeLogOverPWork_vm27
import Theorems.Thm_PI_PrimeLogOverPWork_vm25
import Theorems.Thm_PI_PrimeLogOverPWork_term_ge
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
private theorem vonMangoldt_mul_div_sub_one_le_floor_div (n d : ℕ) (c x : ℝ) (hc : Λ d = c) (hx : (d : ℝ) = x) :
    c * ((n : ℝ) / x - 1) ≤ c * ((n / d : ℕ) : ℝ) := by
  subst hc hx
  exact term_ge n d
end PI.PrimeLogOverPWork
end

set_option autoImplicit false
open PI PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
namespace PI.PrimeLogOverPWork
theorem _root_.solution (n : ℕ) :
    Real.log 2 * ((n : ℝ) * (7 / 16) - 3) + Real.log 3 * ((n : ℝ) * (4 / 27) - 2)
      + Real.log 5 * ((n : ℝ) / 25 - 1) ≤ ∑ d ∈ E, Λ d * ((n / d : ℕ) : ℝ) := by
  have hs : ∑ d ∈ E, Λ d * ((n / d : ℕ) : ℝ) =
      Λ 4 * ((n / 4 : ℕ) : ℝ) + (Λ 8 * ((n / 8 : ℕ) : ℝ) + (Λ 16 * ((n / 16 : ℕ) : ℝ) +
        (Λ 9 * ((n / 9 : ℕ) : ℝ) + (Λ 27 * ((n / 27 : ℕ) : ℝ) + Λ 25 * ((n / 25 : ℕ) : ℝ))))) := by
    rw [E, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),
      Finset.sum_singleton]
  rw [hs, vm4, vm8, vm16, vm9,
    vm27, vm25]
  have h4 := vonMangoldt_mul_div_sub_one_le_floor_div n 4 (Real.log 2) 4 vm4 (by norm_num)
  have h8 := vonMangoldt_mul_div_sub_one_le_floor_div n 8 (Real.log 2) 8 vm8 (by norm_num)
  have h16 := vonMangoldt_mul_div_sub_one_le_floor_div n 16 (Real.log 2) 16 vm16 (by norm_num)
  have h9 := vonMangoldt_mul_div_sub_one_le_floor_div n 9 (Real.log 3) 9 vm9 (by norm_num)
  have h27 := vonMangoldt_mul_div_sub_one_le_floor_div n 27 (Real.log 3) 27 vm27 (by norm_num)
  have h25 := vonMangoldt_mul_div_sub_one_le_floor_div n 25 (Real.log 5) 25 vm25 (by norm_num)
  linarith
end PI.PrimeLogOverPWork
