-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.WOnLatG.exp_pi_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:49:05.390829+00:00
-- url     : https://prove2.me/submissions/739f4ae1-6bb9-46f8-85fd-65e2d3485f3a

import Definitions.Def_Formalism_PeriodIntegrals_WOnLatG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilLatticeAction_NegOneZpowOddMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.WOnLatG
open PI.WPhDefs
namespace PI.UnitaryGroupMassFormula.WOnLatG
theorem _root_.solution (m : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
  have h : (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]
end PI.UnitaryGroupMassFormula.WOnLatG
