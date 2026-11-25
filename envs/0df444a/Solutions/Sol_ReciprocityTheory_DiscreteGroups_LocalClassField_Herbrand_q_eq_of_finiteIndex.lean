-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.q_eq_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:15:22.332995+00:00
-- url     : https://prove2.me/submissions/8bf66acd-3eb9-4cac-b914-4c5faa14c8d8

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_ses_coker
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_SES_DN_C
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_SES_swap
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_isFin_of_finite
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_q_mul
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_q_of_finite


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
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) (hA : IsFin DA NA) :
    q DA NA = q DB NB := by
  have h := ses_coker hf fD fN DN ND
  rw [q_mul h hA (isFin_of_finite _ _), q_of_finite _ _ h.DN_C h.swap.DN_C, mul_one]
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
