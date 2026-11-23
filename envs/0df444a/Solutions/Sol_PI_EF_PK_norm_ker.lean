-- Prove2me | solution 1 for PI.EF.PK.norm_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:12.744612+00:00
-- url     : https://prove2.me/submissions/0aaee6e4-fa92-4b5a-b74d-d4917fa0d9af

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
theorem _root_.solution (l : ℝ) (s : ℂ) : ‖ker l s‖ = Real.exp (l * s.re) / ‖s‖ := by
  unfold ker
  rw [norm_div, Complex.norm_exp, Complex.re_ofReal_mul]
end PI.EF.PK
