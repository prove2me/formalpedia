-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.valueGroup_le_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:29.438383+00:00
-- url     : https://prove2.me/submissions/2ee42ee1-6e2f-492d-bdae-0490f03b6949

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_finDim_extendScalars_of_le
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_norm_algebraNorm
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_one_lt_p_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (hK : FiniteDimensional ℚ_[p] K) :
    valueGroup p K ≤ AddSubgroup.zmultiples
      ((Module.finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (IntermediateField.extendScalars (bot_le : ⊥ ≤ K)) : ℝ)⁻¹) := by
  rintro _ ⟨x, hx, rfl⟩
  have := finDim_extendScalars_of_le p hK (bot_le : ⊥ ≤ K)
  set n := Module.finrank (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
        (IntermediateField.extendScalars (bot_le : ⊥ ≤ K)) with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hn' : (n : ℝ) ≠ 0 := by positivity
  set y : PadicAlgCl p := ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) with hy
  have hy0 : y ≠ 0 := Units.ne_zero _
  have h1 := norm_algebraNorm p hK (bot_le : ⊥ ≤ K) ⟨y, hx⟩
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 (Algebra.norm (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p))
    (⟨y, hx⟩ : IntermediateField.extendScalars (bot_le : ⊥ ≤ K))).2
  rw [← ha, PadicAlgCl.norm_extends] at h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [norm_zero] at h1
    exact (pow_ne_zero _ (norm_ne_zero_iff.2 hy0)) h1.symm
  rw [Padic.norm_eq_zpow_neg_valuation ha0] at h1
  refine AddSubgroup.mem_zmultiples_iff.2 ⟨a.valuation, ?_⟩
  rw [vbar_apply]
  have h2 := congrArg (Real.logb p) h1
  rw [← Real.rpow_intCast, Real.logb_rpow (by linarith [one_lt_p_real p]) (one_lt_p_real p).ne', Real.logb_pow] at h2
  change _ = (n : ℝ) * Real.logb p ‖y‖ at h2
  rw [zsmul_eq_mul]
  push_cast at h2
  field_simp
  linarith
end ReciprocityTheory.DiscreteGroups.LocalClassField
