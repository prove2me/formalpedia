-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isGalois_Kn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:29.560695+00:00
-- url     : https://prove2.me/submissions/a59e6e69-ccc0-4b26-90fd-f8244fb0de9c

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_map_mem_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_le_Kn
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_map_mem_Kn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 Polynomial
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsGalois K (IntermediateField.extendScalars (le_Kn p K n)) := by
  have hnorm : Normal K (IntermediateField.extendScalars (le_Kn p K n)) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    rintro σ _ ⟨x, hx, rfl⟩
    exact map_mem_Kn p K n σ hx
  exact ⟨⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
