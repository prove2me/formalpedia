-- Prove2me | solution 1 for WangGreenTech.Regulation.proposition_4
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T03:23:43.010227+00:00
-- url     : https://prove2.me/submissions/0ed73a52-5899-407e-afb0-a73f8f0b352a

import Mathlib

open MeasureTheory Set

theorem solution : ¬ (∀ (ε b q r f₁ fL fH mL mH qhat : ℝ)
    (hε : 0 < ε) (hb0 : 0 ≤ b) (hq0 : 0 ≤ q) (hq1 : q < 1) (hr : 0 < r)
    (hf₁ : 0 < f₁) (hfL : 0 < fL) (hfH : fL ≤ fH) (hm : mL ≤ mH) (hmH : mH ≤ 0)
    (hqh0 : 0 < qhat) (hqh1 : qhat < 1) (hb : b ≤ 2 * ε)
    (hcal : qhat = q + (1 - q) / (r + 1)),
  let t : ℝ := b / 2 + fL - fH + r / (r + 1) * (1 - q) * (fH - mL)
  let that : ℝ := b / 2 + fL - (1 - qhat) * mL - qhat * fH
  let A : ℝ → ℝ → ℝ := fun cutoff θ => min 1 (max 0 ((θ + ε - cutoff) / (2 * ε)))
  let E : ℝ → (ℝ → ℝ) → ℝ := fun x h =>
    ∫ θ, h θ ∂((ENNReal.ofReal (2 * ε))⁻¹ • volume.restrict (Icc (x - ε) (x + ε)))
  let UD : ℝ → ℝ → ℝ := fun lam x => E x (fun θ =>
    lam - f₁ + mL + θ - b * A t θ + (q + (1 - q) * (A t θ) ^ r) * (mH - mL))
  let UF : ℝ → ℝ → ℝ := fun lam x => E x (fun θ =>
    lam - f₁ + θ - b * A that θ + qhat * mH + (1 - qhat) * mL)
  ∃ lamhat : ℝ, ∀ lam : ℝ, 0 ≤ lam →
    (sInf {x : ℝ | 0 ≤ UD lam x} ≤ sInf {x : ℝ | 0 ≤ UF lam x} ↔ lam ≤ lamhat)) := by
  intro H
  obtain ⟨lamhat, hl⟩ := H 1 0 0 1 1 1 1 0 0 (1/2) one_pos le_rfl le_rfl (by norm_num) one_pos
    one_pos one_pos le_rfl le_rfl le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h2 := hl (|lamhat| + 1) (by positivity)
  simp only [zero_mul, sub_zero, mul_zero, add_zero, sub_self, zero_add, one_mul, Real.rpow_one] at h2
  have h3 := h2.mp le_rfl
  linarith [le_abs_self lamhat]
