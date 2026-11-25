-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.kbar_cocycle_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:33:58.322467+00:00
-- url     : https://prove2.me/submissions/252facf0-8051-494c-a495-c0f2757edefe

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_FiveTerm
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KbarRepContAction
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_RestrictedMultiplicativeH1Subsingleton
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_exists_units_of_continuous_cocycle

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
theorem _root_.solution (H : Subgroup (GK p K)) (f : H → KbarMult p) (hf : Continuous f)
    (hc : ∀ g h : H, f (g * h) = f g + kbarRep p K g (f h)) :
    ∃ m : KbarMult p, ∀ h : H, f h = kbarRep p K h m - m := by
  obtain ⟨β, hβ⟩ := exists_units_of_continuous_cocycle H
    (X := KbarMult p) (Additive.toMul : Additive (PadicAlgCl p)ˣ ≃ (PadicAlgCl p)ˣ) f hf
    (fun g h => congrArg (Additive.toMul : Additive (PadicAlgCl p)ˣ → (PadicAlgCl p)ˣ) (hc g h))
  exact ⟨(Additive.ofMul β : Additive (PadicAlgCl p)ˣ), fun h =>
    congrArg (Additive.ofMul : (PadicAlgCl p)ˣ → Additive (PadicAlgCl p)ˣ) (hβ h)⟩
end ReciprocityTheory.DiscreteGroups.LocalClassField
