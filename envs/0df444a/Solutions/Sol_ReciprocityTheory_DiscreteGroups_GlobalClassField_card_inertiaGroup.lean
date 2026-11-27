-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.card_inertiaGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:27:42.679624+00:00
-- url     : https://prove2.me/submissions/bb917946-5056-45b7-9b2a-3da6e705a345

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_inertiaGroup_eq_inertia

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
include v
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution : Nat.card (inertiaGroup K L Q) = Q.ramificationIdx (𝓞 K) := by
  rw [inertiaGroup_eq_inertia]
  exact (Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal Q).trans
    (Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (L ≃ₐ[K] L))
end ReciprocityTheory.DiscreteGroups.GlobalClassField
