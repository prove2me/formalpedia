-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.card_characters_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:15:19.260903+00:00
-- url     : https://prove2.me/submissions/93e771ed-6150-407a-807e-fb83fd347ecc

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_QZDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecAbA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_pullChar_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_pullChar_injective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_pullChar_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Function
noncomputable section
variable {G : Type} [Group G] [TopologicalSpace G] {A : Type} [AddCommGroup A] (π : Additive G →+ A)
  (hc : IsLocallyConstant fun g : G => π (Additive.ofMul g))
variable {π}
include hc
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution [Finite A] (hπ : Surjective π) :
    Nat.card {χ : charGrp G // ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0} = Nat.card A := by
  rw [← card_hom_QZ A]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun ψ : A →+ QZ => (⟨pullChar π hc ψ, fun g hg => by rw [pullChar_apply, hg, map_zero]⟩ :
      {χ : charGrp G // ∀ g : G, π (Additive.ofMul g) = 0 → χ.1 (Additive.ofMul g) = 0})) ⟨?_, ?_⟩)).symm
  · intro ψ ψ' h
    exact pullChar_injective hc hπ (congrArg Subtype.val h)
  · rintro ⟨χ, hχ⟩
    obtain ⟨ψ, hψ⟩ := exists_pullChar_eq hc hπ χ hχ
    exact ⟨ψ, Subtype.ext hψ⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
