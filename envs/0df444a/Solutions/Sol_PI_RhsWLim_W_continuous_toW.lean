-- Prove2me | solution 1 for PI.RhsWLim.W.continuous_toW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:57.038215+00:00
-- url     : https://prove2.me/submissions/5a51cc94-1673-442b-9b20-e355e198a038

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
theorem _root_.solution : Continuous (toW k) := by
  refine continuous_pi fun j => ?_
  by_cases h : j.val < k
  · have : (fun p : (Fin k → ℂ) × ℂ => toW k p j) = fun p => p.1 ⟨j.val, h⟩ := by
      funext p; unfold toW; rw [dif_pos h]
    rw [this]
    exact (continuous_apply _).comp continuous_fst
  · have : (fun p : (Fin k → ℂ) × ℂ => toW k p j) = fun p => p.2 := by
      funext p; unfold toW; rw [dif_neg h]
    rw [this]
    exact continuous_snd
end PI.RhsWLim.W
