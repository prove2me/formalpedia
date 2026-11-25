-- Prove2me | solution 1 for PI.SSE.qf_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:04.318992+00:00
-- url     : https://prove2.me/submissions/5ffdad48-dabd-4f50-ad75-52b49d1b0fac

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_LatExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Classical
open PI PI.SSE
namespace PI.SSE
theorem _root_.solution (A ω z : ℂ) (hA : A ≠ 0) : qf A ω (z + -ω) * qf A (-ω) z = 1 := by
  simp only [qf, map_neg]
  rw [← Complex.exp_add, ← Complex.exp_zero]
  congr 1
  field_simp
  ring
end PI.SSE
