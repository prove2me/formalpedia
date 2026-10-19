-- Prove2me | solution 1 for PELiquidity.Secondary.eq_C6
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T19:07:36.712124+00:00
-- url     : https://prove2.me/submissions/8c3c9e0f-d64d-4de7-afcc-da7d8d0a6edf

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

/-- (C.6): minimum H-LP primary-market return. Top-level `solution`
    matching platform target 56a40026-52be-4e80-9248-ccdc0c9defcd. -/
theorem solution (P : PELiquidity.Primary.Params) (D Rb : ℝ)
    (hDlo : 1 - P.δH ≤ D) (hDhi : D ≤ 1 - P.δL) :
    (1 - P.lam + P.lam * P.δH / (1 - D) =
      Rb * (1 - P.lam + P.lam * P.δH) ↔
      Rb = 1 + P.lam * P.δH * D / (1 - D) * PELiquidity.Primary.grossReturn P.lam P.δH) := by
  obtain ⟨hDpos, hD01⟩ : (0 : ℝ) < D ∧ D < 1 :=
    ⟨by linarith [hDlo, P.hδH1], by linarith [hDhi, P.hδL0]⟩
  have hne1 : (1 - D : ℝ) ≠ 0 := by linarith
  have hAp : (0 : ℝ) < 1 - P.lam + P.lam * P.δH := by
    have h0 : (0 : ℝ) < 1 - P.lam := by linarith [P.hlam1]
    have h1 : (0 : ℝ) < P.lam * P.δH := mul_pos P.hlam0 P.hδH0
    linarith
  have hAne : (1 - P.lam * (1 - P.δH) : ℝ) ≠ 0 := by
    rw [show (1 - P.lam * (1 - P.δH) : ℝ) = 1 - P.lam + P.lam * P.δH by ring]
    exact ne_of_gt hAp
  have hgr : PELiquidity.Primary.grossReturn P.lam P.δH = 1 / (1 - P.lam * (1 - P.δH)) := rfl
  constructor
  · intro h
    rw [hgr]
    have h1 : P.lam * P.δH / (1 - D) =
        Rb * (1 - P.lam + P.lam * P.δH) - (1 - P.lam) := by linarith
    rw [div_eq_iff hne1] at h1
    field_simp [hAne]
    linarith [h1]
  · intro h
    rw [h, hgr]
    field_simp [hne1, hAne]
    ring
