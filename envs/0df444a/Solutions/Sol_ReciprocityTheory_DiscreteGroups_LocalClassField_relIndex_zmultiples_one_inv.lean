-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.relIndex_zmultiples_one_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:54.313824+00:00
-- url     : https://prove2.me/submissions/440e32b0-a499-4fe2-9cc7-6f6ece787db0

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_divHom_injective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_map_divHom_zmultiples
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_map_divHom_top

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
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    (AddSubgroup.zmultiples (1 : ℝ)).relIndex (AddSubgroup.zmultiples ((n : ℝ)⁻¹)) = n := by
  rw [← map_divHom_zmultiples hn, ← map_divHom_top,
    AddSubgroup.relIndex_map_map_of_injective _ _ (divHom_injective hn), AddSubgroup.relIndex_top_right,
    Int.index_zmultiples, Int.natAbs_natCast]
end ReciprocityTheory.DiscreteGroups.LocalClassField
