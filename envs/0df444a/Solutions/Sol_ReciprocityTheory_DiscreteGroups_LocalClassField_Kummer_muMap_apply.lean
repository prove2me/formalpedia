-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.muMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:14.857994+00:00
-- url     : https://prove2.me/submissions/d0a1e2bf-77fb-4bb4-a8b0-a52a4da589c4

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowLES
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
open _root_.Neutral.B1
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]
variable {p n}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
theorem _root_.solution (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (k : ZMod n) :
    muMap ζ hζ k = (Additive.ofMul (ζ ^ k.val) : KbarMult p) := rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
