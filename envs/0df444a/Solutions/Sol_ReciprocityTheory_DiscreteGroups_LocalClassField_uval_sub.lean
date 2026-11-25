-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.uval_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:13.207997+00:00
-- url     : https://prove2.me/submissions/e13f25f7-3aaa-4d7a-abf9-e1255aa3c776

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_add
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_uval_neg

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
theorem _root_.solution (a b : (layerU p K L).V) : uval (a - b) = uval a * (uval b)⁻¹ := by
  rw [sub_eq_add_neg, uval_add, uval_neg]
end ReciprocityTheory.DiscreteGroups.LocalClassField
