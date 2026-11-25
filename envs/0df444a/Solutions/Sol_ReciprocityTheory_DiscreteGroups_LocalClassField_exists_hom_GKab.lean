-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_hom_GKab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:02.046292+00:00
-- url     : https://prove2.me/submissions/2d1fd6a6-a1ed-439b-a244-55c73cf5663b

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_IsAbLK_normal
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_toAbK_eq_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_of_compatible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
open Topology
open scoped commutatorElement
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {A : Type*} [Group A] (γ : IntermediateField ℚ_[p] (PadicAlgCl p) → A → GK p K)
    (hmul : ∀ L, IsAbLK p K L → ∀ a b, (γ L (a * b))⁻¹ * (γ L a * γ L b) ∈ subG p K L)
    (hγ : ∀ L L', IsAbLK p K L → IsAbLK p K L' → L ≤ L' → ∀ a, (γ L a)⁻¹ * γ L' a ∈ subG p K L) :
    ∃ f : A →* GKab p K, ∀ L, IsAbLK p K L → ∀ (a : A) (g : GK p K), toAbK p K g = f a →
      (γ L a)⁻¹ * g ∈ subG p K L := by
  have hex : ∀ a, ∃ g : GK p K, ∀ L, IsAbLK p K L → (γ L a)⁻¹ * g ∈ subG p K L := fun a =>
    exists_of_compatible hK (fun L => γ L a) fun L L' hL hL' hle => hγ L L' hL hL' hle a
  choose s hs using hex
  refine ⟨MonoidHom.mk' (fun a => toAbK p K (s a)) fun a b => ?_, fun L hL a g hg => ?_⟩
  · rw [← map_mul, toAbK_eq_iff hK]
    intro L hL
    have := hL.normal
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, ← QuotientGroup.eq.2 (hs a L hL), ← QuotientGroup.eq.2 (hs b L hL),
      ← QuotientGroup.eq.2 (hs (a * b) L hL), ← QuotientGroup.mk_mul]
    exact QuotientGroup.eq.2 (hmul L hL a b)
  · have h1 : (s a)⁻¹ * g ∈ subG p K L := (toAbK_eq_iff hK (s a) g).1 hg.symm L hL
    have h2 : (γ L a)⁻¹ * g = ((γ L a)⁻¹ * s a) * ((s a)⁻¹ * g) := by group
    rw [h2]
    exact mul_mem (hs a L hL) h1
end ReciprocityTheory.DiscreteGroups.LocalClassField
