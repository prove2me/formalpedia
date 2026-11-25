-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.relIndex_pos_of_le_zmultiples
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:14.858423+00:00
-- url     : https://prove2.me/submissions/a8d4bab0-9c6c-4386-920d-9589cb5d46d9

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_relIndex_zmultiples_one_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (V : AddSubgroup ℝ) (h1 : (1 : ℝ) ∈ V) {n : ℕ} (hn : 0 < n)
    (hV : V ≤ AddSubgroup.zmultiples ((n : ℝ)⁻¹)) : 0 < (AddSubgroup.zmultiples (1 : ℝ)).relIndex V := by
  have h2 := AddSubgroup.relIndex_mul_relIndex (AddSubgroup.zmultiples (1 : ℝ)) V _
    (AddSubgroup.zmultiples_le_of_mem h1) hV
  rw [relIndex_zmultiples_one_inv hn] at h2
  exact Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at h2; omega
end ReciprocityTheory.DiscreteGroups.LocalClassField
