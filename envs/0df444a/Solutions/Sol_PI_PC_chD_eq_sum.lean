-- Prove2me | solution 1 for PI.PC.chD_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:25:05.054047+00:00
-- url     : https://prove2.me/submissions/727d6037-5319-4118-83aa-6de19d9f6cac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
import Theorems.Thm_PI_PC_log_factorial_eq_sum
import Theorems.Thm_PI_PC_log_factorial_eq_sum_of_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.PC
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta
private theorem nat_floor_div_natCast (x : ℝ) (k : ℕ) : ⌊x / (k : ℝ)⌋₊ = ⌊x⌋₊ / k :=
  Nat.floor_div_natCast x k
end PI.PC
end
end

set_option autoImplicit false
noncomputable section
open PI PI.PC
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta
namespace PI.PC
theorem _root_.solution (x : ℝ) : chD x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * chE (⌊x⌋₊ / d) := by
  have hL : ∀ k : ℕ, lf (x / (k : ℝ)) =
      ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (((⌊x⌋₊ / d) / k : ℕ) : ℝ) := by
    intro k
    unfold lf
    rw [nat_floor_div_natCast, log_factorial_eq_sum_of_le (Nat.div_le_self ⌊x⌋₊ k)]
    apply Finset.sum_congr rfl
    intro d _
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm k d]
  have h1 : lf x = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ((⌊x⌋₊ / d : ℕ) : ℝ) := by
    unfold lf
    exact log_factorial_eq_sum _
  have h2 := hL 2
  have h3 := hL 3
  have h5 := hL 5
  have h30 := hL 30
  push_cast at h2 h3 h5 h30
  unfold chD
  rw [h1, h2, h3, h5, h30]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold chE
  ring
end PI.PC
