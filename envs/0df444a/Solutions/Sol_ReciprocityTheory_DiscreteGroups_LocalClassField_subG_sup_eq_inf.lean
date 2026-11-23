-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.subG_sup_eq_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:34.407097+00:00
-- url     : https://prove2.me/submissions/c6df1ebf-7f47-4b2a-8027-ac4fd5cfb14a

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RecDefs
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GabLim
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
open Topology
open scoped commutatorElement
variable {p K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (L L' : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    subG p K (L ⊔ L') = subG p K L ⊓ subG p K L' := by
  refine le_antisymm (le_inf (subG_anti le_sup_left) (subG_anti le_sup_right)) fun σ hσ => ?_
  have hle : L ⊔ L' ≤ (IntermediateField.fixedField (Subgroup.zpowers σ)).restrictScalars ℚ_[p] := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ.1 : Subgroup.zpowers σ ≤ subG p K L) hτ x hx
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ.2 : Subgroup.zpowers σ ≤ subG p K L') hτ x hx
  intro x hx
  have := hle hx
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff] at this
  exact this σ (Subgroup.mem_zpowers σ)
end ReciprocityTheory.DiscreteGroups.LocalClassField
