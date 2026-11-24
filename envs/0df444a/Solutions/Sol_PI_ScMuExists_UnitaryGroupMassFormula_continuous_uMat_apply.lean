-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.continuous_uMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:18:47.814944+00:00
-- url     : https://prove2.me/submissions/b52a562e-b760-4fe8-9f33-162817881ecf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (v : NumberField.InfinitePlace I.F) :
    Continuous fun s : I.Ginf => Formalism.MainNotions.S.uMat (s v) := (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)
end PI.ScMuExists.UnitaryGroupMassFormula
