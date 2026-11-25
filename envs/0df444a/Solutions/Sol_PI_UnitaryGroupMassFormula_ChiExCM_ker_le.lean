-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ChiExCM.ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:43:30.123178+00:00
-- url     : https://prove2.me/submissions/92045b0b-7845-49a7-a57f-478fa0702eb7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ChiExCM
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharExtend
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneCharacters_NormOneCharacterApply
import Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_mem_normOne
import Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_iota_val
import Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_lam_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_ChiExCM_kron_step

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
theorem _root_.solution (c : E →+* E) (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x))
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (hμ : ∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → ∏ s, emb s x = 1) :
    (iota c).ker ≤ (lam c S emb).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  have h1 : Submodule.span (𝓞 E) {((u : Eˣ) : E)} = 1 := by
    rw [← iota_val, hu, Units.val_one]
  ext
  rw [lam_apply, Finset.prod_inv_distrib, hμ _ (kron_step c hc _ ((mem_normOne c _).1 u.2) h1), inv_one, Units.val_one]
end PI.UnitaryGroupMassFormula.ChiExCM
