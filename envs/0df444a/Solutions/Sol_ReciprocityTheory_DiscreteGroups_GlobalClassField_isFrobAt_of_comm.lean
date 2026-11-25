-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:06.902086+00:00
-- url     : https://prove2.me/submissions/7e0fb30b-3fdd-4877-891e-bc295f4da829

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isFrobAt_smul
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_exists_smul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped Pointwise
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {K L}
variable (v : HeightOneSpectrum (𝓞 K)) (Q Q' : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
variable [IsGalois K L]
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution (hc : ∀ a b : L ≃ₐ[K] L, a * b = b * a) [Q'.IsPrime]
    [Q'.LiesOver v.asIdeal] (τ : L ≃ₐ[K] L) (h : IsFrobAt K L τ Q) : IsFrobAt K L τ Q' := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq v Q Q'
  have := isFrobAt_smul σ τ Q h
  rwa [hc σ τ, mul_inv_cancel_right] at this
end ReciprocityTheory.DiscreteGroups.GlobalClassField
