-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_subG_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:54.587486+00:00
-- url     : https://prove2.me/submissions/b3d3cba7-fbfd-42c7-ac5d-e4415605caf6

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
theorem _root_.solution (U : Subgroup (GK p K)) (hU : IsClosed (U : Set (GK p K))) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ L ∧ subG p K L = U := by
  have h : K ≤ (IntermediateField.fixedField U).restrictScalars ℚ_[p] :=
    fun x hx => (IntermediateField.fixedField U).algebraMap_mem ⟨x, hx⟩
  refine ⟨_, h, ?_⟩
  rw [subG_eq_fixingSubgroup h]
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨U, hU⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
