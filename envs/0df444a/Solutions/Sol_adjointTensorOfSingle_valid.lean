-- Prove2me | solution 1 for adjointTensorOfSingle_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:08:57.234907+00:00
-- url     : https://prove2.me/submissions/15d3db4f-8943-4bdb-ad98-270b6c3e24c6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FockRBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_OkSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FilterConcatWLength
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_MultidegSingle
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_StepMonoFactor
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AdjointTensorOfSingleValid
import Theorems.Thm_PI_TOW_DegW_stepDeg
import Theorems.Thm_PI_TOW_LiftW_stepLift
import Theorems.Thm_PI_TOW_MonoW_stepMonoFactor
import Theorems.Thm_PI_TOW_stepPure_of
import Theorems.Thm_PI_TOW_stepSpan
import Theorems.Thm_PI_TOW_tenOp_of_steps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.TenOp :=
  PI.TOW.tenOp_of_steps PI.TOW.DegW.stepDeg
    (PI.TOW.stepPure_of PI.TOW.LiftW.stepLift PI.TOW.MonoW.stepMonoFactor) PI.TOW.stepSpan
