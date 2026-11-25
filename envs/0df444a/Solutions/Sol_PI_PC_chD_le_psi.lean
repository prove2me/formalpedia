-- Prove2me | solution 1 for PI.PC.chD_le_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:31:20.012005+00:00
-- url     : https://prove2.me/submissions/9653c2bf-276f-4cd0-aaca-1b1579d044ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
import Theorems.Thm_PI_PC_chE_le_one
import Theorems.Thm_PI_PC_chD_eq_sum
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
private theorem chebyshev_psi_eq_sum_Ioc_vonMangoldt (x : ℝ) : ψ x = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n := by
  rfl
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
theorem _root_.solution (x : ℝ) : chD x ≤ ψ x := by
  rw [chD_eq_sum, chebyshev_psi_eq_sum_Ioc_vonMangoldt]
  apply Finset.sum_le_sum
  intro d _
  have hc := chE_le_one (⌊x⌋₊ / d)
  have h0 : 0 ≤ Λ d := ArithmeticFunction.vonMangoldt_nonneg
  exact mul_le_of_le_one_right h0 hc
end PI.PC
