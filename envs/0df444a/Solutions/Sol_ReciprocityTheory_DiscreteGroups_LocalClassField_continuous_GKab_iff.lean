-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.continuous_GKab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:40.724799+00:00
-- url     : https://prove2.me/submissions/963305bd-66f4-46bf-b825-610e7b4c315d

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_toAbK_surjective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_toAbK_eq_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_coset_subset
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_coset_mem_nhds

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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {X : Type*} [TopologicalSpace X] (f : X → GKab p K) :
    Continuous f ↔ ∀ L, IsAbLK p K L → ∀ x, ∀ᶠ y in 𝓝 x, ∀ g g' : GK p K, toAbK p K g = f x → toAbK p K g' = f y →
      g⁻¹ * g' ∈ subG p K L := by
  constructor
  · intro hf L hL x
    obtain ⟨g₀, hg₀⟩ := toAbK_surjective (f x)
    have hn := coset_mem_nhds hL g₀
    rw [hg₀] at hn
    filter_upwards [hf.continuousAt hn] with y hy g g' hg hg'
    obtain ⟨g₁, hg₁, hg₁y⟩ := hy
    have h1 : g⁻¹ * g₀ ∈ subG p K L := (toAbK_eq_iff hK g g₀).1 (hg.trans hg₀.symm) L hL
    have h2 : g₁⁻¹ * g' ∈ subG p K L := (toAbK_eq_iff hK g₁ g').1 (hg₁y.trans hg'.symm) L hL
    have h3 : g⁻¹ * g' = (g⁻¹ * g₀) * (g₀⁻¹ * g₁) * (g₁⁻¹ * g') := by group
    rw [h3]
    exact mul_mem (mul_mem h1 hg₁) h2
  · intro h
    rw [continuous_iff_continuousAt]
    intro x W hW
    obtain ⟨g₀, hg₀⟩ := toAbK_surjective (f x)
    rw [← hg₀] at hW
    obtain ⟨L, hL, hsub⟩ := exists_coset_subset hK g₀ W hW
    rw [Filter.mem_map]
    filter_upwards [h L hL x] with y hy
    obtain ⟨g₁, hg₁⟩ := toAbK_surjective (f y)
    show f y ∈ W
    rw [← hg₁]
    exact hsub g₁ (hy g₀ g₁ hg₀ hg₁)
end ReciprocityTheory.DiscreteGroups.LocalClassField
