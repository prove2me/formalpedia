-- Prove2me | solution 1 for PI.RhsWLim.W.ZetaZeros.meas_wD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:35:59.456968+00:00
-- url     : https://prove2.me/submissions/16ded560-f3ba-4067-a70a-3c4e883a98b6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_TBallMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_HaarUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
open PI.RhsWLim.W.ZetaZeros
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
namespace PI.RhsWLim.W.ZetaZeros
theorem _root_.solution : Measurable (wD k r z z') := by
  have hn : Measurable (fun ζ : ℂ => Complex.normSq ζ) := Complex.continuous_normSq.measurable
  have hz : Measurable (zWeight k (Tz k r z) (Tz k r z')) := by
    unfold zWeight
    exact Measurable.ite (measurableSet_le measurable_const hn) ((hn.sub measurable_const).pow_const _)
      measurable_const
  unfold wD
  exact Measurable.ite (measurableSet_lt measurable_const hn) (ENNReal.measurable_ofReal.comp hz) measurable_const
end PI.RhsWLim.W.ZetaZeros
