-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ChiExCM.mem_normOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:10.737891+00:00
-- url     : https://prove2.me/submissions/97415222-5b90-4eb5-a8f0-b95a67b83334

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
theorem _root_.solution (c : E →+* E) (u : Eˣ) : u ∈ normOne c ↔ (u : E) * c u = 1 := Iff.rfl
end PI.UnitaryGroupMassFormula.ChiExCM
