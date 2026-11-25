-- Prove2me | solution 1 for PI.SSE.zsign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:16:06.945892+00:00
-- url     : https://prove2.me/submissions/cde9091f-b8d1-4150-8d5b-b0c2a54cca93

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
theorem _root_.solution (a b k c : ℤ) (h : Even (a + b + k - c)) :
    (-1 : ℂ) ^ a * (-1 : ℂ) ^ b * (-1 : ℂ) ^ k = (-1 : ℂ) ^ c := by
  have h1 : (-1 : ℂ) ≠ 0 := by norm_num
  rw [← zpow_add₀ h1, ← zpow_add₀ h1, show a + b + k = c + (a + b + k - c) by ring, zpow_add₀ h1,
    h.neg_one_zpow, mul_one]
end PI.SSE
