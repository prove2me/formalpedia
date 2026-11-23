-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:55.480993+00:00
-- url     : https://prove2.me/submissions/3f2efdc2-e24d-4185-96ce-7124e747b582

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_eq_fixingSubgroup

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
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) :
    degLK p K L = Module.finrank K (IntermediateField.extendScalars h) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← subG_eq_fixingSubgroup h]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
