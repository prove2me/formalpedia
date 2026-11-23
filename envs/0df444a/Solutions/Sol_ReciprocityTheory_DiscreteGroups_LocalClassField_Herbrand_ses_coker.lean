-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.ses_coker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:31.489896+00:00
-- url     : https://prove2.me/submissions/d4a6dc75-97a0-4e6c-9103-e876cffb1b43

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB

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
theorem _root_.solution (hf : Injective f)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) :
    SES DA NA DB NB (cokerMap f fD) (cokerMap f fN) f (QuotientAddGroup.mk' f.range) where
  inj := hf
  exact := fun b => by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  surj := QuotientAddGroup.mk'_surjective _
  fD := fD
  fN := fN
  gD := fun _ => rfl
  gN := fun _ => rfl
  DN := DN
  ND := ND
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
