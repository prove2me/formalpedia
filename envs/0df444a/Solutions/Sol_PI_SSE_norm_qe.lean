-- Prove2me | solution 1 for PI.SSE.norm_qe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:01.653186+00:00
-- url     : https://prove2.me/submissions/e5b50135-b2bf-43e6-904d-92602fccf026

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaNz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (τ : ℂ) (n : ℕ) :
    ‖qe τ n‖ = Real.exp (-(Real.pi * τ.im * ((n : ℝ) * ((n : ℝ) + 1)))) := by
  rw [qe, Complex.norm_exp]
  congr 1
  have e : (Real.pi : ℂ) * I * τ * ((n : ℂ) * ((n : ℂ) + 1)) =
      ((Real.pi * ((n : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ) * (I * τ) := by
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, Complex.I_mul_re]
  ring
end PI.SSE
