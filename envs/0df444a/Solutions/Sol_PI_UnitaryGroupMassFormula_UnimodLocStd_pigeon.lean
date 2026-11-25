-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.pigeon
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:46:03.682166+00:00
-- url     : https://prove2.me/submissions/2a6c4289-21c3-45a9-b4ad-8a8d99f3eaf4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_DescentStep
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open Polynomial
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) (A B E : ℤ) (hA : ¬ (p : ℤ) ∣ A)
    (hB : ¬ (p : ℤ) ∣ B) : ∃ s t : ℤ, (p : ℤ) ∣ s ^ 2 * A + t ^ 2 * B - E := by
  have := Fact.mk hp
  have hA' : (A : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hB' : (B : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hf : (C (A : ZMod p) * X ^ 2 - C (E : ZMod p)).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hA']; norm_num), degree_C_mul_X_pow 2 hA']
    rfl
  have hg : (C (B : ZMod p) * X ^ 2).degree = 2 := by
    rw [degree_C_mul_X_pow 2 hB']
    rfl
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg (by rw [ZMod.card]; exact hodd)
  refine ⟨(x.val : ℤ), (y.val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hxy
  linear_combination hxy
end PI.UnitaryGroupMassFormula.UnimodLocStd
