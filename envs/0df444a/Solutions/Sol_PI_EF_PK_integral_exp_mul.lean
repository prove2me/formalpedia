-- Prove2me | solution 1 for PI.EF.PK.integral_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:37:03.149562+00:00
-- url     : https://prove2.me/submissions/934a4c16-ce42-42b0-9fd2-c16f87e25874

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real
namespace PI.EF.PK
theorem _root_.solution (l a b : ℝ) (hl : l ≠ 0) :
    ∫ x in a..b, Real.exp (l * x) = (Real.exp (l * b) - Real.exp (l * a)) / l := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hl, integral_exp, smul_eq_mul]
  ring
end PI.EF.PK
