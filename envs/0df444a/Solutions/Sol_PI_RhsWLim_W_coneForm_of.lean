-- Prove2me | solution 1 for PI.RhsWLim.W.coneForm_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:14:30.874924+00:00
-- url     : https://prove2.me/submissions/5070d8a1-e013-4e71-95d0-17a4ac0892b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushC

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
namespace PI.RhsWLim.W
theorem _root_.solution (hH : HypTh) (hV : ConeVol) : ConeForm := by
  intro k T' hT'
  obtain ⟨c1, h10, h1t, h1⟩ := hH k T' hT'
  obtain ⟨c2, h20, h2t, h2⟩ := hV k T' hT'
  refine ⟨c1 / c2, ENNReal.div_pos h10 h2t |>.ne', ENNReal.div_ne_top h1t h20, fun E hE => ?_⟩
  rw [h1 E hE, h2 E hE, ← mul_assoc, ENNReal.div_mul_cancel h20 h2t]
end PI.RhsWLim.W
