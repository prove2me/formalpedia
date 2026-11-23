-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ChiExCM.lam_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:44:08.8638+00:00
-- url     : https://prove2.me/submissions/9e6af1be-53c9-45c2-8117-94895b741c81

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
theorem _root_.solution (c : E →+* E) (S : Type) [Fintype S] (emb : S → E →+* ℂ) (u : normOne c) :
    ((lam c S emb u : ℂˣ) : ℂ) = ∏ s, (emb s ((u : Eˣ) : E))⁻¹ := by
  simp [lam, Units.coe_prod, Finset.prod_inv_distrib]
end PI.UnitaryGroupMassFormula.ChiExCM
