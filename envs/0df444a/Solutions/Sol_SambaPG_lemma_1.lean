-- Prove2me | solution 1 for SambaPG.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:05:12.306404+00:00
-- url     : https://prove2.me/submissions/e876899a-5999-4216-8098-bdc168590c36

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (qbar : ℕ → ℝ) (hpos : ∀ t, 0 < qbar t) {η : ℝ} (hη : 0 < η)
    (h7 : ∀ t, qbar (t + 1) ≤ qbar t - η * qbar t ^ 2) :
    ∀ t : ℕ, qbar t ≤ qbar 0 / (1 + η * qbar 0 * t) := by
  have hinv : ∀ t : ℕ, 1 / qbar 0 + η * t ≤ 1 / qbar t := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
      have hqt := hpos t
      have hqt1 := hpos (t + 1)
      have hstep : 1 / qbar t + η ≤ 1 / qbar (t + 1) := by
        rw [div_add' _ _ _ (ne_of_gt hqt), div_le_div_iff₀ hqt hqt1]
        have hle : qbar (t + 1) ≤ qbar t := by
          have := h7 t
          nlinarith [sq_nonneg (qbar t)]
        have hmul : η * qbar t * qbar (t + 1) ≤ η * qbar t * qbar t :=
          mul_le_mul_of_nonneg_left hle (mul_nonneg (le_of_lt hη) (le_of_lt hqt))
        have hsq : η * qbar t * qbar t = η * qbar t ^ 2 := by ring
        linarith [h7 t]
      push_cast
      linarith
  intro t
  have hq0 := hpos 0
  have hqt := hpos t
  have hden : 0 < 1 + η * qbar 0 * t := by positivity
  have hi := hinv t
  have h1 : (1 + η * qbar 0 * t) / qbar 0 ≤ 1 / qbar t := by
    have heq : (1 + η * qbar 0 * t) / qbar 0 = 1 / qbar 0 + η * t := by
      field_simp [ne_of_gt hq0]
    linarith
  rw [div_le_div_iff₀ hq0 hqt] at h1
  rw [le_div_iff₀ hden]
  linarith
