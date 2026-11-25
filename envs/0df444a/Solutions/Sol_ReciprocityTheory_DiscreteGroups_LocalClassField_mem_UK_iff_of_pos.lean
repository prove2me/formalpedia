-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_UK_iff_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:43.466102+00:00
-- url     : https://prove2.me/submissions/a5bb0d44-f34b-4d85-87ad-e8d51c4140be

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_le_one_iff_vK_of_pos
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_lt_one_iff_vK_of_pos

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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (he : 0 < eK p K) (x : Kˣ) : x ∈ UK p K ↔ vK p K x = 0 := by
  show ‖((x : K) : PadicAlgCl p)‖ = 1 ↔ _
  have h1 := norm_le_one_iff_vK_of_pos p K he x
  have h2 := norm_lt_one_iff_vK_of_pos p K he x
  constructor
  · intro h
    have h3 := h1.1 h.le
    have h4 : ¬ (1 ≤ vK p K x) := fun h5 => (h2.2 h5).ne h
    omega
  · intro h
    have h3 := h1.2 (by omega)
    have h4 : ¬ ‖((x : K) : PadicAlgCl p)‖ < 1 := fun h5 => by have := h2.1 h5; omega
    exact le_antisymm h3 (not_lt.1 h4)
end ReciprocityTheory.DiscreteGroups.LocalClassField
