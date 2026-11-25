-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isIntegralClosure_OK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:40:21.676391+00:00
-- url     : https://prove2.me/submissions/8c36fe02-3259-4bd7-82f5-b04e3df16bdf

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_isIntegral_zp_K_iff
import Theorems.Thm_ReciprocityTheory_Neutral_Cmp_norm_le_one_iff_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution : IsIntegralClosure (OK p K) ℤ_[p] K where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    rw [isIntegral_zp_K_iff, ← norm_le_one_iff_isIntegral, ← mem_OK_iff]
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
