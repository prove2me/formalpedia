-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.denseRange_GKab_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:45.262746+00:00
-- url     : https://prove2.me/submissions/ee72856d-b29b-41b2-b8c4-a89972b1df24

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_toAbK_surjective
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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {X : Type*} (f : X → GKab p K) :
    DenseRange f ↔ ∀ L, IsAbLK p K L → ∀ g : GK p K, ∃ (x : X) (g' : GK p K), toAbK p K g' = f x ∧
      g'⁻¹ * g ∈ subG p K L := by
  constructor
  · intro hf L hL g
    obtain ⟨x, g', hg', hx⟩ := hf.mem_nhds (coset_mem_nhds hL g)
    refine ⟨x, g', hx, ?_⟩
    have : g'⁻¹ * g = (g⁻¹ * g')⁻¹ := by group
    rw [this]
    exact inv_mem hg'
  · intro h y
    obtain ⟨g, rfl⟩ := toAbK_surjective y
    rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨L, hL, hsub⟩ := exists_coset_subset hK g W hW
    obtain ⟨x, g', hg', hx⟩ := h L hL g
    refine ⟨f x, ?_, x, rfl⟩
    rw [← hg']
    refine hsub g' ?_
    have : g⁻¹ * g' = (g'⁻¹ * g)⁻¹ := by group
    rw [this]
    exact inv_mem hx
end ReciprocityTheory.DiscreteGroups.LocalClassField
