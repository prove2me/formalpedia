-- Prove2me | solution 1 for TechSourcing.PTS.lemma_A1_phiHat
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:09:26.793914+00:00
-- url     : https://prove2.me/submissions/853cce75-4d38-473d-ad44-8ac2ac86021d

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model

open TechSourcing.PTS in
theorem solution (P : Params) (hP : P.Standing) (θ : ℝ) (hθ : θ ≤ 1) (φ : ℝ) :
    IsExistingBR P θ φ ↔ φ = phiHat P θ := by
  obtain ⟨_, _, hc, hD, _, _, hβ1⟩ := hP
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = P.D * (1 - P.β) * (1 - θ) / (2 * P.c) := ⟨_, rfl⟩
  have hu : u * (2 * P.c) = P.D * (1 - P.β) * (1 - θ) := by
    rw [hu_def]; field_simp
  have hu0 : 0 ≤ u := by
    rw [hu_def]
    exact div_nonneg (mul_nonneg (mul_nonneg hD.le (sub_nonneg.mpr hβ1)) (sub_nonneg.mpr hθ))
      (by positivity)
  have hph : phiHat P θ = 1 - u := by rw [hu_def]; rfl
  have hid : ∀ φ' : ℝ, UO P θ φ' = UO P θ (1 - u) - P.c * (φ' - (1 - u)) ^ 2 := by
    intro φ'
    unfold UO
    linear_combination (-(1 - φ' - u)) * hu
  rw [hph]
  constructor
  · rintro ⟨_, hmax⟩
    have h1 := hmax (1 - u) (by linarith)
    rw [hid φ] at h1
    have h0 : (φ - (1 - u)) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg (φ - (1 - u))]) (sq_nonneg _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    linarith
  · rintro rfl
    refine ⟨by linarith, fun φ' _ => ?_⟩
    rw [hid φ']
    nlinarith [sq_nonneg (φ' - (1 - u))]
