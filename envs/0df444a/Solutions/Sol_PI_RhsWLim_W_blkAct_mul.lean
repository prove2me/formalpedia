-- Prove2me | solution 1 for PI.RhsWLim.W.blkAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:52.975797+00:00
-- url     : https://prove2.me/submissions/b0e7233c-a92b-4a8a-ad6a-346ad14af45b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_RhsTest
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushI
import Theorems.Thm_PI_RhsWLim_W_toW_ofW

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
theorem _root_.solution (μ ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) :
    blkAct k μ (blkAct k ν p) = blkAct k (μ * ν) p := by
  unfold blkAct
  rw [toW_ofW, Matrix.mulVec_mulVec]
end PI.RhsWLim.W
