-- Prove2me | solution 1 for PI.ScPiBuildW.Asm.cont_uMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:19:12.155579+00:00
-- url     : https://prove2.me/submissions/adfca97a-0f7d-4c15-b5e0-3c6057517125

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocalFramePreservesOrthogonal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_LocFrame
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_ContinuousOnTensOp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorFrameConstruction_InnerOfNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open scoped InnerProductSpace
open PI PI.ScPiBuildW PI.ScPiBuildW.Asm
open PI.ScPiExists Formalism.MainNotions.S
namespace PI.ScPiBuildW.Asm
theorem _root_.solution (I : AutInst) (v : InfinitePlace I.F) : Continuous fun s : I.Ginf => uMat (s v) :=
  Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
end PI.ScPiBuildW.Asm
