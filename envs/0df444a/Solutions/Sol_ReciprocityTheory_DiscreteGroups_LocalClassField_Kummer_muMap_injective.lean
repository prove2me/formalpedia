-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.muMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:47.68581+00:00
-- url     : https://prove2.me/submissions/cc54605e-767d-4781-8af0-64e07032dbd3

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
theorem _root_.solution {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : Function.Injective (muMap ζ hζ.pow_eq_one) := by
  intro a b hab
  exact ZMod.val_injective n (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab)
end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
