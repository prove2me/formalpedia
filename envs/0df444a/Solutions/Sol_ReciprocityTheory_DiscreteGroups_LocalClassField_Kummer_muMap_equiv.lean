-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.muMap_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:16.870473+00:00
-- url     : https://prove2.me/submissions/008537e0-a289-48ab-9bb1-126830dd3371

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowLES
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_kbarRep_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_muRep_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_muMap_apply
import Theorems.Thm_Neutral_B1_cycN_spec


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
theorem _root_.solution (ζ : (PadicAlgCl p)ˣ) (hζ : ζ ^ n = 1) (g : GK p K) (k : ZMod n) :
    muMap ζ hζ (muRep p K n g k) = kbarRep p K g (muMap ζ hζ k) := by
  rw [muMap_apply, muMap_apply, kbarRep_apply, muRep_apply]
  refine congrArg Additive.ofMul (Units.ext ?_)
  have h1 : ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, Units.val_one]
  have h2 := cycN_spec (K := K) g _ h1
  show _ = g ((ζ ^ k.val : (PadicAlgCl p)ˣ) : PadicAlgCl p)
  rw [h2, ← Units.val_pow_eq_pow_val, ZMod.val_mul, ← pow_eq_pow_mod _ hζ, ← pow_mul, mul_comm]
end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
