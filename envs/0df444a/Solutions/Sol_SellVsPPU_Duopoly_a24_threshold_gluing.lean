-- Prove2me | solution 1 for SellVsPPU.Duopoly.a24_threshold_gluing
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:13:55.640366+00:00
-- url     : https://prove2.me/submissions/b283df3d-d45a-4bee-9a6b-16bf8f3a38f3

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model
namespace SellVsPPU.Duopoly

/-- Stronger than printed: p. 42 states the meeting value at c = a*q_m/3; this theorem reconciles both full regime comparisons with Proposition 3. -/
theorem _root_.solution (P : Params) (hP : P.Admissible) :
    (P.c ≤ P.qm * (P.a / 2 - P.delta) →
      (P.delta ≤ P.c / (2 * P.qm) ↔ P.delta ≤ deltaBar P.a P.qm P.c)) ∧
    (P.qm * (P.a / 2 - P.delta) < P.c →
      (P.delta ≤ P.a - P.c / P.qm -
        2 * P.a * ((P.a * P.qm - P.c) / (P.a * P.qm + P.c)) ^ 2 ↔
        P.delta ≤ deltaBar P.a P.qm P.c)) := by
  obtain ⟨ha, hq, hc, hd, hadm⟩ := hP
  set x := P.c / (P.a * P.qm) with hx
  set d := P.delta / P.a with hdd
  have haq : 0 < P.a * P.qm := mul_pos ha hq
  have hx0 : 0 < x := div_pos hc haq
  have hd0 : 0 ≤ d := div_nonneg hd ha.le
  have ec : P.c = x * (P.a * P.qm) := by rw [hx]; field_simp
  have ed : P.delta = P.a * d := by rw [hdd]; field_simp
  have hx1 : x + d ≤ 1 := by
    have : P.c / P.qm = P.a * x := by rw [ec]; field_simp
    rw [this, ed] at hadm
    nlinarith
  have e1 : P.c / (2 * P.qm) = P.a * (x / 2) := by rw [ec]; field_simp
  have er : (P.a * P.qm - P.c) / (P.a * P.qm + P.c) = (1 - x) / (1 + x) := by
    rw [ec]
    have : (1:ℝ) + x ≠ 0 := by positivity
    field_simp
  have e2 : P.a - P.c / P.qm - 2 * P.a * ((P.a * P.qm - P.c) / (P.a * P.qm + P.c)) ^ 2
      = P.a * (1 - x - 2 * ((1 - x) / (1 + x)) ^ 2) := by
    rw [er]
    have : P.c / P.qm = P.a * x := by rw [ec]; field_simp
    rw [this]; ring
  have i : ∀ y, P.delta ≤ P.a * y ↔ d ≤ y := fun y => by rw [ed]; exact mul_le_mul_iff_right₀ ha
  have c3 : P.c ≤ P.a * P.qm / 3 ↔ x ≤ 1 / 3 := by
    rw [hx, div_le_iff₀ haq]; constructor <;> intro h <;> linarith
  have r1 : P.c ≤ P.qm * (P.a / 2 - P.delta) ↔ x ≤ 1 / 2 - d := by
    have : P.qm * (P.a / 2 - P.delta) = (1 / 2 - d) * (P.a * P.qm) := by rw [ed]; ring
    rw [this, hx, div_le_iff₀ haq]
  have r2 : P.qm * (P.a / 2 - P.delta) < P.c ↔ 1 / 2 - d < x := by
    rw [← not_le, r1, not_le]
  have h1 : (0:ℝ) < 1 + x := by linarith
  have big : 1 / 3 ≤ x → (1 / 2 - x) ≤ 1 - x - 2 * ((1 - x) / (1 + x)) ^ 2 := by
    intro h
    have : ((1 - x) / (1 + x)) ^ 2 ≤ (1 / 2) ^ 2 := by
      apply pow_le_pow_left₀ (div_nonneg (by linarith) h1.le)
      rw [div_le_iff₀ h1]; linarith
    linarith
  have small : x ≤ 1 / 3 → 1 - x - 2 * ((1 - x) / (1 + x)) ^ 2 ≤ 1 / 2 - x := by
    intro h
    have : (1 / 2) ^ 2 ≤ ((1 - x) / (1 + x)) ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num)
      rw [le_div_iff₀ h1]; linarith
    linarith
  unfold deltaBar
  rw [r1, r2, e2]
  constructor
  · intro hr
    split_ifs with h
    · exact Iff.rfl
    · rw [e1, i, i]
      rw [c3] at h; push_neg at h
      have := big h.le
      constructor <;> intro _ <;> linarith
  · intro hr
    split_ifs with h
    · rw [c3] at h
      rw [e1, i, i]
      have := small h
      constructor <;> intro h' <;> exfalso <;> linarith
    · exact Iff.rfl


end SellVsPPU.Duopoly

