-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:43.723265+00:00
-- url     : https://prove2.me/submissions/8ca992de-9944-47ec-89ad-1455099cef43

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isFrobAt_iff_forall
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_under_smul_ideal

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
theorem _root_.solution (σ τ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) (h : IsFrobAt K L τ Q) :
    IsFrobAt K L (σ * τ * σ⁻¹) (σ • Q) := by
  rw [isFrobAt_iff_forall] at h ⊢
  intro x
  rw [under_smul_ideal, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  simpa [smul_sub, mul_smul] using h (σ⁻¹ • x)
end ReciprocityTheory.DiscreteGroups.GlobalClassField
