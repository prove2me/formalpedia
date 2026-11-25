-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.uval_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:55.714891+00:00
-- url     : https://prove2.me/submissions/c04c4bfe-d4d3-4837-a3df-1a68eca28d4d

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_add

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
variable [(subG p K L).Normal]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → (layerU p K L).V) :
    uval (∑ i ∈ s, f i) = ∏ i ∈ s, uval (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, uval_add, ih]
end ReciprocityTheory.DiscreteGroups.LocalClassField
