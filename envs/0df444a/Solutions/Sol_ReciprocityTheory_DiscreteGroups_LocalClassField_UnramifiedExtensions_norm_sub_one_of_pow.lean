-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions.norm_sub_one_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:59:02.361103+00:00
-- url     : https://prove2.me/submissions/f6fa743a-a845-44cb-9f9c-ee3ad425d4a9

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrDefs
import Definitions.Def_Lemmata_PadicNatCastNorm_NormNatCastOfNotDvd
import Definitions.Def_Lemmata_FirstBlockLemmaC_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaD_Imports
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_NormSubEqOneOfPowEqOne
import Theorems.Thm_Bl_FirstBlockLemmaC_goal1
import Theorems.Thm_Bl_FirstBlockLemmaD_goal1
import Theorems.Thm_Bl_PadicNatCastNorm_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField
variable {p : ℕ} [Fact p.Prime]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
theorem _root_.solution {m : ℕ} (hm : ¬ p ∣ m) {η : PadicAlgCl p} (hη : η ^ m = 1) (h : η ≠ 1) :
    ‖η - 1‖ = 1 := by
  first | exact Bl.PadicNatCastNorm.goal1 .. | (apply Bl.PadicNatCastNorm.goal1 <;> assumption) | (intros; apply Bl.PadicNatCastNorm.goal1 <;> assumption)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
