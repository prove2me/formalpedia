-- Prove2me | solution 1 for PI.PC.chE_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:10.411063+00:00
-- url     : https://prove2.me/submissions/ccbfc514-7a15-425d-b127-98ef65f88e6f

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
theorem _root_.solution {q : ℕ} (h1 : 1 ≤ q) (h6 : q < 6) : chE q = 1 := by
  have h : q / 2 + q / 3 + q / 5 + 1 = q + q / 30 := by omega
  have h' : ((q / 2 : ℕ) : ℝ) + ((q / 3 : ℕ) : ℝ) + ((q / 5 : ℕ) : ℝ) + 1 = (q : ℝ) + ((q / 30 : ℕ) : ℝ) := by
    exact_mod_cast h
  unfold chE
  linarith
end PI.PC
