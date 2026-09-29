-- Prove2me | solution 1 for VectorSpaceOpt.min_norm_duality_dual_space
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T13:21:07.096073+00:00
-- url     : https://prove2.me/submissions/d04e1967-4a4e-404b-b385-1bbc9facbb59

import Mathlib
import Definitions.Def_VectorSpaceOpt_aligned


theorem solution {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (f : X →L[ℝ] ℝ) :
    ∃ g₀ : X →L[ℝ] ℝ, (∀ m ∈ M, g₀ m = 0) ∧
      (∀ g : X →L[ℝ] ℝ, (∀ m ∈ M, g m = 0) → ‖f - g₀‖ ≤ ‖f - g‖) ∧
      ‖f - g₀‖ = sSup {r : ℝ | ∃ x ∈ M, ‖x‖ ≤ 1 ∧ r = f x} ∧
      (∀ x₀ ∈ M, ‖x₀‖ ≤ 1 → f x₀ = ‖f - g₀‖ →
        VectorSpaceOpt_aligned x₀ (f - g₀)) := by
  classical
  set fM : M →L[ℝ] ℝ := f.comp M.subtypeL with hfM
  obtain ⟨F, hFext, hFnorm⟩ := exists_extension_norm_eq M fM
  refine ⟨f - F, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have := hFext ⟨m, hm⟩
    simp only [ContinuousLinearMap.sub_apply]
    rw [this, hfM]
    simp
  · intro g hg
    have hfg : f - (f - F) = F := by ext x; simp
    rw [hfg, hFnorm]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro m
    have hgm : (f - g) m = f m := by
      simp only [ContinuousLinearMap.sub_apply, hg m m.2, sub_zero]
    have : fM m = (f - g) (m : X) := by rw [hfM]; simp [hgm]
    rw [this]
    exact (f - g).le_opNorm _
  · have hfg : f - (f - F) = F := by ext x; simp
    rw [hfg, hFnorm]
    set A : Set ℝ := {r : ℝ | ∃ x ∈ M, ‖x‖ ≤ 1 ∧ r = f x} with hA
    have hAne : A.Nonempty := ⟨0, ⟨0, M.zero_mem, by simp, by simp⟩⟩
    refine (csSup_eq_of_forall_le_of_forall_lt_exists_gt hAne ?_ ?_).symm
    · rintro r ⟨x, hx, hx1, rfl⟩
      have h1 : f x = fM ⟨x, hx⟩ := by rw [hfM]; simp
      have h2 : fM ⟨x, hx⟩ ≤ ‖fM ⟨x, hx⟩‖ := le_abs_self _
      have h3 : ‖fM ⟨x, hx⟩‖ ≤ ‖fM‖ * ‖(⟨x, hx⟩ : M)‖ := fM.le_opNorm _
      have h4 : ‖(⟨x, hx⟩ : M)‖ = ‖x‖ := rfl
      rw [h1]
      nlinarith [norm_nonneg fM, norm_nonneg x]
    · intro ub hub
      obtain ⟨y, hy1, hy2⟩ := fM.exists_lt_apply_of_lt_opNorm hub
      rcases le_or_gt 0 (fM y) with h | h
      · refine ⟨fM y, ⟨(y : X), y.2, le_of_lt hy1, ?_⟩, ?_⟩
        · rw [hfM]; simp
        · rwa [Real.norm_eq_abs, abs_of_nonneg h] at hy2
      · refine ⟨fM (-y), ⟨((-y : M) : X), (-y).2, ?_, ?_⟩, ?_⟩
        · show ‖((-y : M) : X)‖ ≤ 1
          have : ‖((-y : M) : X)‖ = ‖(y : X)‖ := by
            simp
          rw [this]; exact le_of_lt hy1
        · rw [hfM]; simp
        · rw [map_neg]
          rwa [Real.norm_eq_abs, abs_of_neg h] at hy2
  · intro x₀ hx₀ hx₀1 hval
    have hfg : f - (f - F) = F := by ext x; simp
    rw [hfg] at hval ⊢
    rw [VectorSpaceOpt_aligned]
    have hFx : F x₀ = f x₀ := by
      have h := hFext ⟨x₀, hx₀⟩
      rw [h, hfM]; simp
    rcases eq_or_lt_of_le (norm_nonneg F) with h0 | hpos
    · rw [hFx, hval, ← h0, zero_mul]
    · have hle : F x₀ ≤ ‖F‖ * ‖x₀‖ := by
        calc F x₀ ≤ ‖F x₀‖ := le_abs_self _
          _ ≤ ‖F‖ * ‖x₀‖ := F.le_opNorm _
      rw [hFx, hval] at hle
      have h1 : (1:ℝ) ≤ ‖x₀‖ := by nlinarith
      rw [hFx, hval, le_antisymm hx₀1 h1, mul_one]
