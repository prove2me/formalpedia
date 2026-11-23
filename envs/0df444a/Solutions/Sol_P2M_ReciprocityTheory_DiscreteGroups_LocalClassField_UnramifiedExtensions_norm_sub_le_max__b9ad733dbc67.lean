-- Prove2me | solution 1 for P2M_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_le_max__b9ad733dbc67
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:19.754189+00:00
-- url     : https://prove2.me/submissions/f265f028-04f9-4574-a1f7-76431e0aa55e

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
theorem _root_.solution (x y : PadicAlgCl p) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  first | exact Bl.FirstBlockLemmaD.goal1 .. | (apply Bl.FirstBlockLemmaD.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaD.goal1 <;> assumption)
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
