-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.subG_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:30.302288+00:00
-- url     : https://prove2.me/submissions/da248e4e-260b-4bbd-9373-9a15d420a829

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_anti
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_subG_sup
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_iff_fixed

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
theorem _root_.solution {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) :
    subG p K L' ≤ subG p K L ↔ L ≤ K ⊔ L' := by
  constructor
  · intro hle x hx
    rw [mem_iff_fixed (le_sup_left : K ≤ K ⊔ L'), subG_sup]
    exact fun σ hσ => hle hσ x hx
  · intro hle
    rw [← subG_sup p K L']
    exact subG_anti hle
end ReciprocityTheory.DiscreteGroups.LocalClassField
