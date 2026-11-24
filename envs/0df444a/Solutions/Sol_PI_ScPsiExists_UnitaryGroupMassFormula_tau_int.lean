-- Prove2me | solution 1 for PI.ScPsiExists.UnitaryGroupMassFormula.tau_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:18:49.8818+00:00
-- url     : https://prove2.me/submissions/2b655e11-de63-426d-aa78-a07e2ec5161f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Theorems.Thm_PI_ScPsiExists_UnitaryGroupMassFormula_tau_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.S
open scoped TensorProduct
open PI PI.ScPsiExists PI.ScPsiExists.UnitaryGroupMassFormula
variable {F E : Type} [Field F] [Field E] [StarRing E] [Algebra F E]
namespace PI.ScPsiExists.UnitaryGroupMassFormula
theorem _root_.solution [NumberField F] [NumberField E]
    (hfix : ∀ a : E, star a = a ↔ a ∈ (algebraMap F E).range) (c : 𝓞 E) :
    ∃ d : 𝓞 F, algebraMap (𝓞 F) F d = tau hfix (algebraMap (𝓞 E) E c) := by
  have h1 : IsIntegral ℤ (algebraMap (𝓞 E) E c) := RingOfIntegers.isIntegral_coe c
  have h2 : IsIntegral ℤ (star (algebraMap (𝓞 E) E c)) := by
    have := h1.map (starRingEnd E).toIntAlgHom
    exact this
  have h3 : IsIntegral ℤ (algebraMap F E (tau hfix (algebraMap (𝓞 E) E c))) := by
    rw [tau_apply]
    exact h1.add h2
  have h4 := (isIntegral_algebraMap_iff (algebraMap F E).injective).1 h3
  exact ⟨⟨_, h4⟩, rfl⟩
end PI.ScPsiExists.UnitaryGroupMassFormula
