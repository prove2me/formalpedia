-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.kbarRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:55:10.219087+00:00
-- url     : https://prove2.me/submissions/b3ca66ed-66d4-4093-9c8a-eca5c688f028

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
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
theorem _root_.solution (σ : GK p K) (x : (PadicAlgCl p)ˣ) :
    kbarRep p K σ (Additive.ofMul x : KbarMult p) =
      (Additive.ofMul (Units.map (σ : PadicAlgCl p →* PadicAlgCl p) x) : KbarMult p) := rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
