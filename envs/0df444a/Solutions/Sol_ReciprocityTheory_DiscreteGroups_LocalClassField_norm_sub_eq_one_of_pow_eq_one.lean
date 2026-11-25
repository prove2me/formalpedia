-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.norm_sub_eq_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:31:48.027074+00:00
-- url     : https://prove2.me/submissions/bd410f1d-4b20-43e2-8c82-52e5e1ea8c00

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_PowPowSuccSub
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnrExtA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnramifiedExtensions_norm_sub_eq_one_of_pow_eq_one


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
theorem _root_.solution {m : ℕ} (hm : ¬ p ∣ m) {ζ ξ : PadicAlgCl p} (hζ : ζ ^ m = 1)
    (hξ : ξ ^ m = 1) (h : ζ ≠ ξ) : ‖ζ - ξ‖ = 1 :=
  UnramifiedExtensions.norm_sub_eq_one_of_pow_eq_one hm hζ hξ h
end ReciprocityTheory.DiscreteGroups.LocalClassField
