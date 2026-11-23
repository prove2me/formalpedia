-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.powMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:50.839067+00:00
-- url     : https://prove2.me/submissions/ab494fa1-394a-4f9f-a603-6cc9c7d301b4

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
theorem _root_.solution (x : (PadicAlgCl p)ˣ) :
    powMap p n (Additive.ofMul x : KbarMult p) = (Additive.ofMul (x ^ n) : KbarMult p) := by
  show (n : ℤ) • (Additive.ofMul x : Additive (PadicAlgCl p)ˣ) = _
  rw [natCast_zsmul]; rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
