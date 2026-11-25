-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:11:11.617274+00:00
-- url     : https://prove2.me/submissions/62a2f152-090f-489b-a10a-0fcb80717e4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_anti
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_range_galois_restriction

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
theorem _root_.solution {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) (h' : L ≤ L') :
    degLK p K L' = degLK p K L * degLK p L L' := by
  have hc : (subG p K L').comap (resGK h) = subG p L L' := rfl
  show (subG p K L').index = (subG p K L).index * (subG p L L').index
  rw [← hc, Subgroup.index_comap, range_galois_restriction, mul_comm,
    Subgroup.relIndex_mul_index (subG_anti h')]
end ReciprocityTheory.DiscreteGroups.LocalClassField
