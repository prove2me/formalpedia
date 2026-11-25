-- Prove2me | solution 1 for PI.RhsWLim.W.toW_ofW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:53:33.370477+00:00
-- url     : https://prove2.me/submissions/9adb96ab-37a7-4c9b-8601-35f41b3de7b5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI

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
open PI.RhsWLim PI.RhsWLim.W.MB
variable {k r : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution (v : Fin (k + 1) → ℂ) : toW k (ofW k v) = v := by
  funext j
  unfold toW ofW
  by_cases h : j.val < k
  · rw [dif_pos h]
    congr 1
  · rw [dif_neg h]
    have : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    rw [this]
end PI.RhsWLim.W
