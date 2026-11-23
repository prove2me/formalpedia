-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.finiteIndex_subG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:02.307473+00:00
-- url     : https://prove2.me/submissions/9d48853f-c7e8-4092-8f34-19cdf03ffec8

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isOpen_subG

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
theorem _root_.solution (hL : FiniteDimensional ℚ_[p] L) : (subG p K L).FiniteIndex := by
  have : Finite (GK p K ⧸ subG p K L) := Subgroup.quotient_finite_of_isOpen _ (isOpen_subG hL)
  exact Subgroup.finiteIndex_of_finite_quotient
end ReciprocityTheory.DiscreteGroups.LocalClassField
