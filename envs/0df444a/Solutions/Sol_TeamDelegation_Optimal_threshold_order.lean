-- Prove2me | solution 1 for TeamDelegation.Optimal.threshold_order
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:47:07.102539+00:00
-- url     : https://prove2.me/submissions/59c76514-060e-4116-bd90-311f01fd9544

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_Model
open TeamDelegation.Optimal

theorem solution(P : Params) (hS : P.Standing)
    (hA1 : P.Assumption1) :
    0 < DeltaMaxA P ∧ 0 < DeltaMaxB P ∧
      0 < DeltaHatA P ∧ DeltaHatA P < DeltaCritA P ∧
      DeltaCritA P < DeltaMaxA P := by
  obtain ⟨he, hδ0, hδ1, hr0, hr1, hq0, hp2⟩ := hS
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hA1
  unfold DeltaMaxA DeltaMaxB DeltaHatA DeltaCritA punishmentMean
  set D := P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0 with hDdef
  set D' := P.p2 - P.p1 * (1 - P.δ * P.r) + P.q1 * P.δ * (1 - P.r) - P.δ * (P.r * P.p0 + (1 - P.r) * P.q0) with hD'def
  have h1r : 0 < 1 - P.r := by linarith
  have hδr : P.δ * P.r < 1 := by nlinarith
  have h1dr : 0 < 1 - P.δ * P.r := by linarith
  have hΔ : 0 < P.p2 - P.p1 := by linarith
  have e1 := mul_nonneg (mul_nonneg hδ0.le hr0) (by linarith : (0:ℝ) ≤ P.p1 - P.p0)
  have e2 := mul_nonneg (mul_nonneg hδ0.le h1r.le) (by linarith : (0:ℝ) ≤ P.q1 - P.q0)
  have hD : 0 < D := by
    have : D = (P.p2 - P.p1) + P.δ * (P.p1 - P.p0) := by rw [hDdef]; ring
    rw [this]; nlinarith
  have hD'eq : D' = (P.p2 - P.p1) + P.δ * P.r * (P.p1 - P.p0) + P.δ * (1 - P.r) * (P.q1 - P.q0) := by
    rw [hD'def]; ring
  have hD' : 0 < D' := by rw [hD'eq]; linarith
  have hN : 0 < P.p1 - (1 - P.δ) * P.q1 - P.δ * (P.r * P.p0 + (1 - P.r) * P.q0) := by
    have : P.p1 - (1 - P.δ) * P.q1 - P.δ * (P.r * P.p0 + (1 - P.r) * P.q0)
        = (1 - P.δ) * (P.p1 - P.q1) + P.δ * (P.r * (P.p1 - P.p0) + (1 - P.r) * (P.p1 - P.q0)) := by ring
    rw [this]
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - P.δ) (by linarith : (0:ℝ) ≤ P.p1 - P.q1)
    have := mul_nonneg hr0 (by linarith : (0:ℝ) ≤ P.p1 - P.p0)
    have := mul_pos h1r (by linarith : (0:ℝ) < P.p1 - P.q0)
    have := mul_pos hδ0 (by linarith : (0:ℝ) < P.r * (P.p1 - P.p0) + (1 - P.r) * (P.p1 - P.q0))
    linarith
  have hN2 : 0 < P.p1 - (P.r * P.p0 + (1 - P.r) * P.q0) := by
    have := mul_nonneg hr0 (by linarith : (0:ℝ) ≤ P.p1 - P.p0)
    have := mul_pos h1r (by linarith : (0:ℝ) < P.p1 - P.q0)
    nlinarith
  refine ⟨div_pos (mul_pos he hN) (mul_pos h1dr hΔ), div_pos (mul_pos he hN2) (mul_pos h1r hΔ),
    div_pos (mul_pos he (by linarith)) hD, ?_, ?_⟩
  · rw [div_lt_div_iff₀ hD hD']
    have hdiff : D - D' = P.δ * (1 - P.r) * ((P.p1 - P.p0) - (P.q1 - P.q0)) := by
      rw [hD'eq, hDdef]; ring
    have f1 : 0 ≤ D - D' := by
      rw [hdiff]; exact mul_nonneg (mul_nonneg hδ0.le h1r.le) (by linarith)
    have f2 := mul_nonneg (by linarith : (0:ℝ) ≤ P.p1 - P.q1) f1
    have f3 := mul_pos (by linarith : (0:ℝ) < (P.p1 - P.q1) - (P.p0 - P.q0)) hD'
    have core : (P.p0 - P.q0) * D' < (P.p1 - P.q1) * D := by nlinarith
    have := mul_lt_mul_of_pos_left core he
    clear_value D D'
    convert this using 1 <;> ring
  · rw [div_lt_div_iff₀ hD' (mul_pos h1dr hΔ)]
    have hX : 0 < (P.p1 - P.q1) * (P.p2 - P.p0) + (P.q1 - P.p0) * D' := by
      rcases le_or_gt P.q1 P.p0 with hc | hc
      · have g1 : 0 ≤ P.p2 - P.p0 - D' := by
          rw [hD'eq]
          have := mul_le_mul_of_nonneg_left (by linarith : P.q1 - P.q0 ≤ P.p1 - P.p0) (mul_nonneg hδ0.le h1r.le)
          have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - P.δ) (by linarith : (0:ℝ) ≤ P.p1 - P.p0)
          nlinarith
        have g2 := mul_nonneg (by linarith : (0:ℝ) ≤ P.p0 - P.q1) g1
        have g3 := mul_pos (by linarith : (0:ℝ) < P.p1 - P.p0) (by linarith : (0:ℝ) < P.p2 - P.p0)
        nlinarith
      · have g2 := mul_pos (by linarith : (0:ℝ) < P.q1 - P.p0) hD'
        have g3 := mul_pos (by linarith : (0:ℝ) < P.p1 - P.q1) (by linarith : (0:ℝ) < P.p2 - P.p0)
        linarith
    have hid : (P.p1 - (1 - P.δ) * P.q1 - P.δ * (P.r * P.p0 + (1 - P.r) * P.q0)) * D'
        - (P.p1 - P.q1) * ((1 - P.δ * P.r) * (P.p2 - P.p1))
        = P.δ * (P.r * ((P.p1 - P.q1) * (P.p2 - P.p0) + (P.q1 - P.p0) * D')
            + (1 - P.r) * (P.q1 - P.q0) * ((P.p1 - P.q1) + D')) := by
      rw [hD'eq]; ring
    have k1 := mul_nonneg hr0 hX.le
    have k2 := mul_pos (mul_pos h1r (by linarith : (0:ℝ) < P.q1 - P.q0)) (by linarith : (0:ℝ) < (P.p1 - P.q1) + D')
    have k3 := mul_pos hδ0 (by linarith : 0 < P.r * ((P.p1 - P.q1) * (P.p2 - P.p0) + (P.q1 - P.p0) * D')
            + (1 - P.r) * (P.q1 - P.q0) * ((P.p1 - P.q1) + D'))
    have core : (P.p1 - P.q1) * ((1 - P.δ * P.r) * (P.p2 - P.p1)) < (P.p1 - (1 - P.δ) * P.q1 - P.δ * (P.r * P.p0 + (1 - P.r) * P.q0)) * D' := by
      linarith
    have := mul_lt_mul_of_pos_left core he
    clear_value D D'
    convert this using 1 <;> ring
