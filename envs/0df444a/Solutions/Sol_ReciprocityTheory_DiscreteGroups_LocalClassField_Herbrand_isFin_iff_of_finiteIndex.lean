-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.isFin_iff_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:45:07.791719+00:00
-- url     : https://prove2.me/submissions/badff40b-32e5-44b9-999d-9793c77fcd9e

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_ses_coker
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_left
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_mid
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_of_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {DA NA : A →+ A} {DB NB : B →+ B} {f : A →+ B}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution (hf : Injective f) (hfi : f.range.FiniteIndex)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) : IsFin DA NA ↔ IsFin DB NB :=
  ⟨fun hA => isFin_mid (ses_coker hf fD fN DN ND) hA (isFin_of_finite _ _),
    fun hB => isFin_left (ses_coker hf fD fN DN ND) hB (isFin_of_finite _ _)⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
