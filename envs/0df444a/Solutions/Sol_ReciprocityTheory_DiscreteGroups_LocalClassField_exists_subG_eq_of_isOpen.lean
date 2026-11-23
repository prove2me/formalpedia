-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.exists_subG_eq_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:29.583812+00:00
-- url     : https://prove2.me/submissions/3f30ba54-0da9-4837-b311-18d10d2cd463

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_eq_fixingSubgroup
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_subG_eq

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
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) (U : Subgroup (GK p K))
    (hU : IsOpen (U : Set (GK p K))) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ L ∧ FiniteDimensional ℚ_[p] L ∧ subG p K L = U := by
  obtain ⟨L, h, hL⟩ := exists_subG_eq U (Subgroup.isClosed_of_isOpen U hU)
  refine ⟨L, h, ?_, hL⟩
  have hfd : FiniteDimensional K (IntermediateField.extendScalars h) := by
    rw [← InfiniteGalois.isOpen_iff_finite, ← subG_eq_fixingSubgroup h, hL]
    exact hU
  exact FiniteDimensional.trans ℚ_[p] K (IntermediateField.extendScalars h)
end ReciprocityTheory.DiscreteGroups.LocalClassField
