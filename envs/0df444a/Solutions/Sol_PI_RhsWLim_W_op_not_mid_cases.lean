-- Prove2me | solution 1 for PI.RhsWLim.W.op_not_mid_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:37.309965+00:00
-- url     : https://prove2.me/submissions/904878e7-e2d2-4b64-a110-f3459a1c104e

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) : ∃ a : Fin r, i = eI k r a ∨ i = esI k r a := by
  have := i.isLt
  by_cases h : i.val < r
  · exact ⟨⟨i.val, h⟩, Or.inl rfl⟩
  · refine ⟨⟨2 * r + k - i.val, by omega⟩, Or.inr ?_⟩
    apply Fin.ext
    simp only [esI]
    omega
end PI.RhsWLim.W
