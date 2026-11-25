-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.mem_inertiaGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:02.711147+00:00
-- url     : https://prove2.me/submissions/e2a15b4b-2725-42cf-9aff-8029a72302ce

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
theorem _root_.solution {Q : Ideal (𝓞 L)} {τ : L ≃ₐ[K] L} :
    τ ∈ inertiaGroup K L Q ↔ ∀ x : 𝓞 L, galRestrict (𝓞 K) K L (𝓞 L) τ x - x ∈ Q :=
  Iff.rfl
end ReciprocityTheory.DiscreteGroups.GlobalClassField
