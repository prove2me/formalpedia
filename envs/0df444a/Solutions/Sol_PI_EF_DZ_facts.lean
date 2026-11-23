-- Prove2me | solution 1 for PI.EF.DZ_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:30.164801+00:00
-- url     : https://prove2.me/submissions/792e07f4-025b-4b4d-92ae-fc57568bf515

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_HalfLeNormLentCtr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormSubCtrSq
import Theorems.Thm_PI_EF_norm_sub_ctr_sq
import Theorems.Thm_PI_EF_ctr_im
import Theorems.Thm_PI_EF_ctr_re
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.EF.ctr_im
attribute [local simp] PI.EF.ctr_re


section
noncomputable section
namespace PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
private lemma Lent_eq_zero_iff_LFunction_eq_zero_of_ne_one (χ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ : ρ ≠ 1) :
    Lent χ ρ = 0 ↔ LFunction χ ρ = 0 := by
  unfold Lent
  split_ifs with h
  · subst h
    simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hρ, sub_eq_zero]
  · exact Iff.rfl
end PI.EF
end
end

set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex Metric Filter Topology Set DirichletCharacter
variable {N : ℕ} [NeZero N]
namespace PI.EF
theorem _root_.solution (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ DZ χ t) :
    ρ ≠ 1 ∧ LFunction χ ρ = 0 ∧ |ρ.im - t| ≤ 3 ∧
      ((0 < ρ.re ∧ ρ.re < 1) ∨ (ρ = 0 ∧ χ.Even ∧ χ ≠ 1)) := by
  obtain ⟨hb, hz⟩ := hρ
  rw [Metric.mem_closedBall, dist_eq_norm] at hb
  have hsq := norm_sub_ctr_sq ρ t
  have hn := norm_nonneg (ρ - ctr t)
  have hx2 : ‖ρ - ctr t‖ ^ 2 ≤ (11 / 4) ^ 2 := by nlinarith
  have hre : -3 / 4 ≤ ρ.re := by nlinarith [sq_nonneg (ρ.im - t)]
  have him : |ρ.im - t| ≤ 3 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (ρ.re - 2)]
  have hne : ρ ≠ 1 := by
    rintro rfl
    unfold Lent at hz
    split_ifs at hz with h
    · subst h
      first
        | exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero _ hz
        | exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero hz
    · exact DirichletCharacter.LFunction_apply_one_ne_zero h hz
  have hL : LFunction χ ρ = 0 := (Lent_eq_zero_iff_LFunction_eq_zero_of_ne_one χ hne).1 hz
  refine ⟨hne, hL, him, ?_⟩
  rcases hZL N χ hχ ρ (by linarith) hne hL with h | h | ⟨rfl, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · norm_num at hre
end PI.EF
