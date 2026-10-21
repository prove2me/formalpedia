-- Prove2me | solution 1 for SkillData.GoldRush.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T01:18:47.352646+00:00
-- url     : https://prove2.me/submissions/601ebc58-6f83-4b6a-8a27-341dae108193

import Mathlib
import Definitions.Def_SkillData_GoldRush_Model

open SkillData.GoldRush

theorem solution (P : Params) (hP : P.Standing) (C : ℝ → ℝ → ℝ) (c τη : ℝ)
    (hτη : 0 < τη) (X : Clarity) (lam α : ℝ) (hE : IsEquilibrium P C c τη X lam α) :
    (α * P.γ < lam * τη → ∃ x : ℝ, X = .finite x) ∧
      (lam * τη ≤ α * P.γ → X = .asIs) := by
  obtain ⟨hθ, hu, hγ, -, -, hZL, hZ⟩ := hP
  obtain ⟨hF, -⟩ := hE
  cases X with
  | asIs =>
    obtain ⟨-, -, -, h, -⟩ := hF
    refine ⟨fun hlt => ?_, fun _ => rfl⟩
    exfalso; linarith [mul_comm α P.γ]
  | finite x =>
    obtain ⟨hx, hl, -, hα, h14, -⟩ := hF
    refine ⟨fun _ => ⟨x, rfl⟩, fun hle => ?_⟩
    exfalso
    unfold Eq14 at h14
    set u := P.τu * α ^ 2 + τη with hu'
    have hupos : 0 < u := by positivity
    have hD : 0 < x * P.ZL + P.τu * α ^ 2 + τη := by positivity
    have hD' : x * P.ZL + P.τu * α ^ 2 + τη = x * P.ZL + u := by rw [hu']; ring
    rw [hD'] at h14 hD
    have hlin : P.γ * α * (x * P.ZH + P.τu * α ^ 2 + τη) = P.γ * α * (x * P.ZH + u) := by
      rw [hu']; ring
    rw [hlin] at h14
    have key : 2 * (P.γ * α) * (x * P.ZH + u) * (x * P.ZL + u)
        = x * (lam * τη) * (u * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL) := by
      field_simp at h14
      linear_combination h14
    have hpos : 0 < u * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL := by
      have : 0 < P.ZH := by linarith
      positivity
    have h1 : x * (lam * τη) * (u * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL)
        ≤ x * (P.γ * α) * (u * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL) := by
      apply mul_le_mul_of_nonneg_right _ hpos.le
      apply mul_le_mul_of_nonneg_left _ hx.le
      linarith [mul_comm α P.γ]
    have h2 : 2 * (x * P.ZH + u) * (x * P.ZL + u)
        - x * (u * (P.ZH + P.ZL) + 2 * x * P.ZH * P.ZL) = x * u * (P.ZH + P.ZL) + 2 * u ^ 2 := by
      ring
    have h3 : 0 < x * u * (P.ZH + P.ZL) + 2 * u ^ 2 := by
      have : 0 < P.ZH := by linarith
      positivity
    have hga : 0 < P.γ * α := by positivity
    nlinarith [mul_pos hga h3]
