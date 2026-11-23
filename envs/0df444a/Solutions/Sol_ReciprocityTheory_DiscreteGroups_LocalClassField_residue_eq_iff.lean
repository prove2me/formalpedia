-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.residue_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:15.614392+00:00
-- url     : https://prove2.me/submissions/e1690fc0-642e-438f-aeab-d953e1099cd0

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_res_eq_iff


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
theorem _root_.solution (x y : Obar p) :
    IsLocalRing.residue (Obar p) x = IsLocalRing.residue (Obar p) y ↔
      ‖(x : PadicAlgCl p) - (y : PadicAlgCl p)‖ < 1 :=
  UnramifiedExtensions.res_eq_iff x y
end ReciprocityTheory.DiscreteGroups.LocalClassField
