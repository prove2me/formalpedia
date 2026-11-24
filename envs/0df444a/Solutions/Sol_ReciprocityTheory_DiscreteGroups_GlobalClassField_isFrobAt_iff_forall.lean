-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_iff_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:01:29.784588+00:00
-- url     : https://prove2.me/submissions/4f39bfc8-6d11-4cef-8073-5f8866aa2d8f

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_galRestrict_apply_eq_smul

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
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution (τ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) :
    IsFrobAt K L τ Q ↔ ∀ x : 𝓞 L, τ • x - x ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ∈ Q := by
  simp only [← galRestrict_apply_eq_smul]
  rfl
end ReciprocityTheory.DiscreteGroups.GlobalClassField
