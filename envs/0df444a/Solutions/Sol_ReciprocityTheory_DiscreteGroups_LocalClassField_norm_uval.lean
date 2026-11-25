-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.norm_uval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:00:12.941593+00:00
-- url     : https://prove2.me/submissions/0c2e2897-b9b5-41cf-9ca1-2ff3ed1ebaf8

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandE
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandF
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vbar_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_Ubar_iff


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
variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
variable [(subG p K L).Normal]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (w : (layerU p K L).V) : ‖uval w‖ = 1 :=
  (vbar_eq_zero_iff _).1 ((mem_Ubar_iff p _).1 (Subtype.property (p := fun x => x ∈ Ubar p) w.1))
end ReciprocityTheory.DiscreteGroups.LocalClassField
