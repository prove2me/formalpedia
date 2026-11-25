-- Prove2me | solution 1 for PI.RhsWLim.W.blkLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:25.021813+00:00
-- url     : https://prove2.me/submissions/c2ceb2fb-36ea-4df3-82d7-63a8e5336042

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushL

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
theorem _root_.solution {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) :
    blkLin k μ p = blkAct k μ p := by
  simp [blkLin, blkAct, wEquiv, Matrix.toLin'_apply]
end PI.RhsWLim.W
