-- Prove2me | solution 1 for PI.CompDegEF.normAbv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:00:20.856063+00:00
-- url     : https://prove2.me/submissions/b18fc99f-b1df-4b7e-a4b9-01efb34ecfe5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_NormLeOneOfInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompletionDegrees_IsEquivAdicAbvNormAbv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.CompDegEF
open IsDedekindDomain NumberField Module Formalism.BasicNotions Formalism.BasicNotions.Loc
namespace PI.CompDegEF
theorem _root_.solution {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (φ : E →+* Om l) (x : E) :
    normAbv φ x = ‖φ x‖ := rfl
end PI.CompDegEF
