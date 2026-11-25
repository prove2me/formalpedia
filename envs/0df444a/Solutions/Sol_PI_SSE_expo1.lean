-- Prove2me | solution 1 for PI.SSE.expo1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:22:21.165346+00:00
-- url     : https://prove2.me/submissions/3ef3e003-4a7b-41af-86e1-2b07980f5aaa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaDerivNe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_ThetaA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_GenEqOf

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
theorem _root_.solution (v₁ p₁ A z : ℂ) (hv₁ : v₁ ≠ 0) (hA : A ≠ 0) :
    Real.pi * p₁ / (2 * A * v₁) * (z + v₁) ^ 2 =
      Real.pi * p₁ * (z + v₁ / 2) / A + Real.pi * p₁ / (2 * A * v₁) * z ^ 2 := by
  field_simp
  ring
end PI.SSE
