-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.subG_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:11.780826+00:00
-- url     : https://prove2.me/submissions/d438a60c-1cab-4d2d-99a0-26cbcc1f7406

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_anti

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
variable {p K L}
variable (p K L)
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution : subG p K (K ⊔ L) = subG p K L := by
  refine le_antisymm (subG_anti le_sup_right) fun σ hσ => ?_
  have hle : K ⊔ L ≤ (IntermediateField.fixedField (Subgroup.zpowers σ)).restrictScalars ℚ_[p] := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact (IntermediateField.fixedField (Subgroup.zpowers σ)).algebraMap_mem ⟨x, hx⟩
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ : Subgroup.zpowers σ ≤ subG p K L) hτ x hx
  intro x hx
  have := hle hx
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff] at this
  exact this σ (Subgroup.mem_zpowers σ)
end ReciprocityTheory.DiscreteGroups.LocalClassField
