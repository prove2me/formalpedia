-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.card_quot_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:40:59.942538+00:00
-- url     : https://prove2.me/submissions/4c96b200-73be-4aa5-89bb-944a583053ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexOf

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.LCG
theorem _root_.solution {M : Type*} [AddCommGroup M] [Module (𝓞 E) M] (S B : Submodule (𝓞 E) M) :
    Nat.card (B ⧸ S.comap B.subtype) = S.toAddSubgroup.relIndex B.toAddSubgroup := rfl
end PI.UnitaryGroupMassFormula.LCG
