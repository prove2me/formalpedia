-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.galRestrict_apply_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:19.900276+00:00
-- url     : https://prove2.me/submissions/af7d4261-8ca6-4bd9-8c98-4036cec8c9f2

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup

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
theorem _root_.solution (τ : L ≃ₐ[K] L) (x : 𝓞 L) :
    galRestrict (𝓞 K) K L (𝓞 L) τ x = τ • x := by
  apply RingOfIntegers.ext
  exact algebraMap_galRestrict_apply (𝓞 K) τ x
end ReciprocityTheory.DiscreteGroups.GlobalClassField
