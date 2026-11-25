-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.inertiaGroup_eq_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:38.352434+00:00
-- url     : https://prove2.me/submissions/b9c3eb2c-4d7e-4009-99a8-ae6e87786cd2

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_mem_inertiaGroup
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
theorem _root_.solution (Q : Ideal (𝓞 L)) :
    inertiaGroup K L Q = Q.toAddSubgroup.inertia (L ≃ₐ[K] L) := by
  ext τ
  rw [mem_inertiaGroup]
  simp only [galRestrict_apply_eq_smul]
  rfl
end ReciprocityTheory.DiscreteGroups.GlobalClassField
