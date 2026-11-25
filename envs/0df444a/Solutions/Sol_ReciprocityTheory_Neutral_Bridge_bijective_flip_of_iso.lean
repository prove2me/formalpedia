-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.bijective_flip_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:38:07.267349+00:00
-- url     : https://prove2.me/submissions/5d5f061f-67b6-4e59-baa1-b7f967d8f1cf

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
import Theorems.Thm_ReciprocityTheory_Neutral_Bridge_bijective_of_iso

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type*} [CommRing R] {A A' B B' C C' : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
  [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution (α : A ≃ₗ[R] A') (β : B ≃ₗ[R] B') (γ : C ≃ₗ[R] C')
    (f : A →ₗ[R] B →ₗ[R] C) (f' : A' →ₗ[R] B' →ₗ[R] C')
    (h : ∀ a b, f' (α a) (β b) = γ (f a b)) (hf : Function.Bijective f'.flip) :
    Function.Bijective f.flip :=
  bijective_of_iso β α γ f.flip f'.flip (fun b a => h a b) hf
end ReciprocityTheory.Neutral.Bridge
