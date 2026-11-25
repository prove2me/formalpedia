-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sum_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:59:06.117295+00:00
-- url     : https://prove2.me/submissions/24cc98e9-9805-4b0c-9941-0c600d421a99

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Definitions.Def_Lemmata_GeneralBFactUpperTerForm_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtB
import Theorems.Thm_Bl_FirstBlockLemmaC_goal1
import Theorems.Thm_Bl_FirstBlockLemmaD_goal1
import Theorems.Thm_Bl_PadicNatCastNorm_goal1
import Theorems.Thm_Bl_general_b_fact_upper_ter_form_goal1


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
open ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
variable {p}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {ι : Type} (s : Finset ι) (g : ι → PadicAlgCl p) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j ∈ s, ‖g j‖ ≤ C) : ‖∑ j ∈ s, g j‖ ≤ C := by
  first | exact Bl.general_b_fact_upper_ter_form.goal1 .. | (apply Bl.general_b_fact_upper_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_ter_form.goal1 <;> assumption)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
