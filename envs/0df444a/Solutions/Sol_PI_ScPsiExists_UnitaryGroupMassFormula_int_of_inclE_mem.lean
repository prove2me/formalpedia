-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.int_of_inclE_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:55.651801+00:00
-- url     : https://prove2.me/submissions/b8b937ad-3fa3-4640-9636-59ab92cd1e5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_int_of_alg_mem
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_tT_tmul
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_tT_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution (τ : E →ₗ[F] F)
    (hτ : ∀ c : 𝓞 E, ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = τ (algebraMap (𝓞 E) E c))
    (x : E) (hx : Formalism.UG.inclE (F := F) (Af F) x ∈ IntAf F E) :
    ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = τ x := by
  have h := tT_mem τ hτ _ hx
  have he : tT τ (Formalism.UG.inclE (F := F) (Af F) x) = algebraMap F (Af F) (τ x) := by
    simp [Formalism.UG.inclE, tT_tmul]
  rw [he] at h
  exact int_of_alg_mem F _ h
end PI.ScPsiExists.UnitaryGroupMassFormula
