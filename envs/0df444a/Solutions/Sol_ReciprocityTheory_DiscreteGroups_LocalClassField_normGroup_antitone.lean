-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.normGroup_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:33:48.852433+00:00
-- url     : https://prove2.me/submissions/e1ba2c0b-1e72-4a86-919d-a12e430589b7

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormOpenA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_mem_multiplicative_group
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_normHom_comp_normHom_of_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_normGrp_iff


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
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L')
    (h : K ≤ L) (h' : L ≤ L') : normGrp p K L' ≤ normGrp p K L := by
  intro x hx
  rw [mem_normGrp_iff] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := hx
  exact ⟨normHom p L L' y, normHom_mem_multiplicative_group hL' y hy, by rw [normHom_comp_normHom_of_le hL' h h' y hy, hxy]⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
