-- Prove2me | solution 1 for PI.PC.log_factorial_eq_sum_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:19:12.057107+00:00
-- url     : https://prove2.me/submissions/a8b51bc4-3c97-43db-a95c-7b55262f4901

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
import Theorems.Thm_PI_PC_log_factorial_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.PC
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta
namespace PI.PC
theorem _root_.solution {N M : ℕ} (h : N ≤ M) :
    log ((N ! : ℕ) : ℝ) = ∑ d ∈ Ioc 0 M, Λ d * ((N / d : ℕ) : ℝ) := by
  rw [log_factorial_eq_sum]
  apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right h)
  intro d hdM hd
  have hd0 : 0 < d := (Finset.mem_Ioc.mp hdM).1
  have hNd : N < d := by
    by_contra hc
    exact hd (Finset.mem_Ioc.mpr ⟨hd0, by omega⟩)
  rw [Nat.div_eq_of_lt hNd]
  simp
end PI.PC
