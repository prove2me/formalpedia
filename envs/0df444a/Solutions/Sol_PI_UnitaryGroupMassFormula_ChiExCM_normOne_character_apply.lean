-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ChiExCM.normOne_character_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:15.683222+00:00
-- url     : https://prove2.me/submissions/d175a786-a451-4aa8-a88c-b0268b095d5d

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
theorem _root_.solution (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ)
    (hker : (iota c).ker ≤ (lam c S emb).ker) (u : normOne c) :
    chi0 c S emb hker ⟨iota c u, MonoidHom.mem_range.2 ⟨u, rfl⟩⟩ = lam c S emb u := by
  have h : (QuotientGroup.quotientKerEquivRange (iota c)).symm ⟨iota c u, MonoidHom.mem_range.2 ⟨u, rfl⟩⟩ =
      (u : normOne c ⧸ (iota c).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [chi0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]
end PI.UnitaryGroupMassFormula.ChiExCM
