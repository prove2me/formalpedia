-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.uMat_inUJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:19:01.696644+00:00
-- url     : https://prove2.me/submissions/75c4bb82-7bf1-4499-8274-31f1c936242b

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
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε (Formalism.MainNotions.S.uMat g) := g.2
end PI.ScMuExists.UnitaryGroupMassFormula
