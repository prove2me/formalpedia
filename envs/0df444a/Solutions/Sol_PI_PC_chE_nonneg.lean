-- Prove2me | solution 1 for PI.PC.chE_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:18.17196+00:00
-- url     : https://prove2.me/submissions/7da2f08b-3b04-4ff0-8695-a2ec43aa2db9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe

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
theorem _root_.solution (q : ℕ) : 0 ≤ chE q := by
  have h : q / 2 + q / 3 + q / 5 ≤ q + q / 30 := by omega
  have h' : ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) ≤ (q : ℝ) + ((q / 30 : ℕ) : ℝ) := by
    exact_mod_cast h
  unfold chE
  linarith
end PI.PC
