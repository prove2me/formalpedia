-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isClosed_subG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:11.145375+00:00
-- url     : https://prove2.me/submissions/f2f7d1d4-f88f-4408-b204-4b795aa2317a

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_eq_fixingSubgroup
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_sup

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
theorem _root_.solution : IsClosed (subG p K L : Set (GK p K)) := by
  rw [← subG_sup, subG_eq_fixingSubgroup le_sup_left]
  exact InfiniteGalois.fixingSubgroup_isClosed _
end ReciprocityTheory.DiscreteGroups.LocalClassField
