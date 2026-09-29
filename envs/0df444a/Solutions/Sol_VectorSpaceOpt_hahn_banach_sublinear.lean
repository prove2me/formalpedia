-- Prove2me | solution 1 for VectorSpaceOpt.hahn_banach_sublinear
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:53:56.928586+00:00
-- url     : https://prove2.me/submissions/c0e92add-b201-4ce2-a454-f04c76b93e2e

import Mathlib


theorem solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : X → ℝ) (hp_add : ∀ x y : X, p (x + y) ≤ p x + p y)
    (hp_smul : ∀ a : ℝ, 0 < a → ∀ x : X, p (a • x) = a * p x)
    (hp_cont : Continuous p)
    (M : Submodule ℝ X) (f : M →ₗ[ℝ] ℝ) (hf : ∀ m : M, f m ≤ p m) :
    ∃ F : X →ₗ[ℝ] ℝ, Continuous F ∧ (∀ m : M, F m = f m) ∧ ∀ x : X, F x ≤ p x := by
  obtain ⟨F, hFext, hFle⟩ :=
    exists_extension_of_le_sublinear (⟨M, f⟩ : X →ₗ.[ℝ] ℝ) p hp_smul hp_add hf
  have hp0 : p 0 = 0 := by
    have h2 := hp_smul 2 (by norm_num) 0
    rw [smul_zero] at h2
    linarith
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, ∀ x : X, ‖x‖ < δ → p x < 1 := by
    have hcont := hp_cont.continuousAt (x := (0 : X))
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδpos, hd⟩ := hcont 1 one_pos
    refine ⟨δ, hδpos, fun x hx => ?_⟩
    have hxd : dist x (0 : X) < δ := by simpa [dist_eq_norm] using hx
    have hb := hd hxd
    rw [Real.dist_eq, hp0, sub_zero] at hb
    exact lt_of_abs_lt hb
  have hpb : ∀ x : X, p x ≤ (2 / δ) * ‖x‖ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [hp0]
    · have hxn : (0:ℝ) < ‖x‖ := norm_pos_iff.2 hx
      have ht : (0:ℝ) < δ / (2 * ‖x‖) := by positivity
      have hnorm : ‖(δ / (2 * ‖x‖)) • x‖ < δ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        have he : δ / (2 * ‖x‖) * ‖x‖ = δ / 2 := by field_simp
        rw [he]; linarith
      have h1 := hδ _ hnorm
      rw [hp_smul _ ht x] at h1
      have h2r : (0:ℝ) < 2 * ‖x‖ := by positivity
      have h3 : δ * p x < 2 * ‖x‖ := by
        have hmul := mul_lt_mul_of_pos_right h1 h2r
        rw [one_mul] at hmul
        have he : δ / (2 * ‖x‖) * p x * (2 * ‖x‖) = δ * p x := by field_simp
        rw [he] at hmul
        exact hmul
      rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
      linarith [h3, (mul_comm δ (p x) : δ * p x = p x * δ)]
  have hFbound : ∀ x : X, ‖F x‖ ≤ (2 / δ) * ‖x‖ := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, le_trans (hFle x) (hpb x)⟩
    have hneg := hFle (-x)
    rw [map_neg] at hneg
    have hp := hpb (-x)
    rw [norm_neg] at hp
    linarith
  exact ⟨F, (F.mkContinuous (2 / δ) hFbound).continuous, hFext, hFle⟩
