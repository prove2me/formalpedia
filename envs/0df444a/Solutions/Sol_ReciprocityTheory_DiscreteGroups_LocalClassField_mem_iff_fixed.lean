-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_iff_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:54.505799+00:00
-- url     : https://prove2.me/submissions/b7ba60f0-14c4-4bb6-ab29-3ebbf81eb2e9

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
theorem _root_.solution (h : K ≤ L) (x : PadicAlgCl p) : x ∈ L ↔ ∀ σ ∈ subG p K L, σ x = x := by
  rw [subG_eq_fixingSubgroup h, ← IntermediateField.mem_fixedField_iff,
    InfiniteGalois.fixedField_fixingSubgroup]
  rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
