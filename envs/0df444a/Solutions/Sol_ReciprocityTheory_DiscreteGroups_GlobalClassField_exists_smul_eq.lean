-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.exists_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:47.847186+00:00
-- url     : https://prove2.me/submissions/0d928b15-aea4-47cb-8ad5-a31a6a6df26e

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
variable (v : HeightOneSpectrum (𝓞 K)) (Q Q' : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
variable [IsGalois K L]
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution [Q'.IsPrime] [Q'.LiesOver v.asIdeal] : ∃ σ : L ≃ₐ[K] L, σ • Q = Q' :=
  Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal Q Q' (L ≃ₐ[K] L)
end ReciprocityTheory.DiscreteGroups.GlobalClassField
