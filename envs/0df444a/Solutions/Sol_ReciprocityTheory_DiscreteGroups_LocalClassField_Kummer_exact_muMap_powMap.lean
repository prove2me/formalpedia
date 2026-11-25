-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer.exact_muMap_powMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:48:37.418263+00:00
-- url     : https://prove2.me/submissions/e68dcec0-408d-49d1-ae2e-1c69ae67f973

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Duality
import Definitions.Def_ReciprocityTheory_GroupCohomology_LowLES
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_KummerA
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_muMap_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kummer_powMap_apply

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
theorem _root_.solution {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Function.Exact (muMap ζ hζ.pow_eq_one) (powMap p n) := by
  intro y
  constructor
  · intro hy
    have h1 : (Additive.toMul y : (PadicAlgCl p)ˣ) ^ n = 1 := by
      have := powMap_apply (p := p) (n := n) (Additive.toMul y)
      exact (this.symm.trans hy : _)
    have h2 : ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨i, hi, hi'⟩ := (IsPrimitiveRoot.coe_units_iff.2 hζ).eq_pow_of_pow_eq_one h2
    have hi'' : ζ ^ i = (Additive.toMul y : (PadicAlgCl p)ˣ) := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hi')
    refine ⟨(i : ZMod n), ?_⟩
    rw [muMap_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hi'']; rfl
  · rintro ⟨k, rfl⟩
    rw [muMap_apply, powMap_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]; rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField.Kummer
