-- Prove2me | solution 1 for PI.ExistsGaugeMeasureForEachRank.W.toCircle_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:27:47.916449+00:00
-- url     : https://prove2.me/submissions/afb447f1-ff2f-47bb-8df9-ec69343c884a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExistsGaugeMeasureForEachRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_DglApplyOff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_OfRealCoordsSmulCenterCoord
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CircleGaugeAction_ContinuousLmulM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology Set Real
open scoped ENNReal
open PI PI.ExistsGaugeMeasureForEachRank PI.ExistsGaugeMeasureForEachRank.W
variable {r : ℕ}
namespace PI.ExistsGaugeMeasureForEachRank.W
theorem _root_.solution (s : ℝ) :
    ((AddCircle.toCircle (s : AddCircle (2 * π)) : Circle) : ℂ) = Complex.exp (s * Complex.I) := by
  rw [AddCircle.toCircle_apply_mk, div_self (ne_of_gt fact_two_pi.out), one_mul, Circle.coe_exp]
end PI.ExistsGaugeMeasureForEachRank.W
