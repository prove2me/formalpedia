-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.under_smul_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:48:07.824286+00:00
-- url     : https://prove2.me/submissions/ebc917b0-558d-4301-bcd8-916715f7d7b3

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
theorem _root_.solution (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) : (σ • Q).under (𝓞 K) = Q.under (𝓞 K) := by
  ext a
  rw [Ideal.mem_under, Ideal.mem_under, Ideal.pointwise_smul_eq_comap, Ideal.mem_comap]
  have : σ⁻¹ • (algebraMap (𝓞 K) (𝓞 L) a) = algebraMap (𝓞 K) (𝓞 L) a := by
    rw [← galRestrict_apply_eq_smul, AlgEquiv.commutes]
  exact iff_of_eq (congrArg (· ∈ Q) this)
end ReciprocityTheory.DiscreteGroups.GlobalClassField
