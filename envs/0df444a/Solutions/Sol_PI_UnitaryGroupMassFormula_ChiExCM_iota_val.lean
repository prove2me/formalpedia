-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ChiExCM.iota_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:02.426617+00:00
-- url     : https://prove2.me/submissions/5d594df3-0f53-4822-ba0f-5cfd6af62e47

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ChiExCM
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharExtend
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneCharacters_NormOneCharacterApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ChiExCM
open NumberField
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.ChiExCM
theorem _root_.solution (c : E →+* E) (u : normOne c) :
    ((iota c u : (Submodule (𝓞 E) E)ˣ) : Submodule (𝓞 E) E) = Submodule.span (𝓞 E) {((u : Eˣ) : E)} := rfl
end PI.UnitaryGroupMassFormula.ChiExCM
