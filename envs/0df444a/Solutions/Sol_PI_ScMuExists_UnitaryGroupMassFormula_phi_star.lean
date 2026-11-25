-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.phi_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:12.522055+00:00
-- url     : https://prove2.me/submissions/23ecce92-ecfa-4d1f-bde6-7f40bc0eeccb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen

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
theorem _root_.solution (v : NumberField.InfinitePlace I.F) (a : I.E) : I.φ v (star a) = star (I.φ v a) :=
  I.cm.cmUnram.2.1 (I.φ v) a
end PI.ScMuExists.UnitaryGroupMassFormula
