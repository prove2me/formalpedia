-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand.q_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:47:56.921984+00:00
-- url     : https://prove2.me/submissions/1e8e171c-40e1-4fed-8f0d-4b6cd62d4a85

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Herbrand_card_eq_ker_mul_range

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
variable {M : Type*} [AddCommGroup M]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
theorem _root_.solution [Finite M] (D N : M →+ M) (hDN : ∀ x, D (N x) = 0) (hND : ∀ x, N (D x) = 0) :
    q D N = 1 := by
  have h1 : Nat.card D.ker = Nat.card (T D N) * Nat.card N.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (N.range.addSubgroupOf D.ker)]
    congr 1
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (by
      rintro _ ⟨x, rfl⟩; exact hDN x)).toEquiv
  have h2 : Nat.card N.ker = Nat.card (T N D) * Nat.card D.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (D.range.addSubgroupOf N.ker)]
    congr 1
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (by
      rintro _ ⟨x, rfl⟩; exact hND x)).toEquiv
  have h3 := card_eq_ker_mul_range D
  have h4 := card_eq_ker_mul_range N
  rw [h1] at h3
  rw [h2] at h4
  have h5 : Nat.card (T D N) * (Nat.card N.range * Nat.card D.range) =
      Nat.card (T N D) * (Nat.card N.range * Nat.card D.range) := by
    calc _ = Nat.card M := by rw [h3]; ring
      _ = _ := by rw [h4]; ring
  have h6 : Nat.card (T D N) = Nat.card (T N D) :=
    Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos) h5
  unfold q
  rw [h6]
  exact div_self (Nat.cast_ne_zero.2 Nat.card_pos.ne')
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
