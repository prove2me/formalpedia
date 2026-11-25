-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.qK_le_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:35:20.206362+00:00
-- url     : https://prove2.me/submissions/55abd085-57fd-4864-bf17-538ef3d792e3

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_comb_injective
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_exists_lifts
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_finrank_fun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hL : FiniteDimensional ℚ_[p] L) (hKL : K ≤ L) :
    ∃ f : ℕ, 0 < f ∧ qK p L = qK p K ^ f ∧ f * Module.finrank ℚ_[p] K ≤ Module.finrank ℚ_[p] L := by
  obtain ⟨f, hf, hq, ω, h1, h2⟩ := UnramifiedExtensions.exists_lifts hL hKL
  refine ⟨f, hf, hq, ?_⟩
  rw [← UnramifiedExtensions.finrank_fun hK]
  exact LinearMap.finrank_le_finrank_of_injective (UnramifiedExtensions.comb_injective hKL ω h1 h2)
end ReciprocityTheory.DiscreteGroups.LocalClassField
