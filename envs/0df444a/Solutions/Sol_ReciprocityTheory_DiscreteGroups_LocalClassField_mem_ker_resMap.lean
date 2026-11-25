-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.mem_ker_resMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:14:42.191825+00:00
-- url     : https://prove2.me/submissions/57137846-cf97-4e0b-a2b5-bd8efd72b0c6

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_residue_eq_iff


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
theorem _root_.solution (x : OK p K) : x ∈ RingHom.ker (resMap p K) ↔ ‖((x : K) : PadicAlgCl p)‖ < 1 := by
  rw [RingHom.mem_ker]
  show IsLocalRing.residue (Obar p) (toObar p K x) = 0 ↔ _
  rw [← map_zero (IsLocalRing.residue (Obar p)), residue_eq_iff]
  show ‖((x : K) : PadicAlgCl p) - 0‖ < 1 ↔ _
  rw [sub_zero]
end ReciprocityTheory.DiscreteGroups.LocalClassField
