-- Prove2me | solution 1 for TechSourcing.PTS.thetaLStar_rewrite
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:42:37.864544+00:00
-- url     : https://prove2.me/submissions/bd82fe67-68ca-4b40-b537-238d25f32ab4

import Mathlib
import Definitions.Def_TechSourcing_PTS_Model
set_option autoImplicit false

open TechSourcing.PTS

lemma aaa_aux (a B d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    (Real.sqrt ((a * B) ^ 2 + 6 * a * d) - a * B) / 6 =
      d / (Real.sqrt (B ^ 2 + 6 / a * d) + B) := by
  have hq : 0 ≤ B ^ 2 + 6 / a * d := by positivity
  have hS2 : Real.sqrt (B ^ 2 + 6 / a * d) ^ 2 = B ^ 2 + 6 / a * d := Real.sq_sqrt hq
  have hS0 : 0 ≤ Real.sqrt (B ^ 2 + 6 / a * d) := Real.sqrt_nonneg _
  generalize Real.sqrt (B ^ 2 + 6 / a * d) = S at hS2 hS0 ⊢
  have h6 : 0 < 6 / a * d := by positivity
  have hpos : 0 < S + B := by
    by_contra h
    push_neg at h
    have h' : S ≤ -B := by linarith
    nlinarith [mul_self_le_mul_self hS0 h']
  have hsq : Real.sqrt ((a * B) ^ 2 + 6 * a * d) = a * S := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have : a * a * S ^ 2 = a * a * (B ^ 2 + 6 / a * d) := by rw [hS2]
    field_simp at this ⊢
    nlinarith [this]
  rw [hsq, div_eq_div_iff (by norm_num) (by linarith)]
  have h2 : (S - B) * (S + B) = 6 / a * d := by nlinarith [hS2]
  field_simp at h2 ⊢
  nlinarith [h2]

theorem solution (P : Params) (hP : P.Standing) (hWL : Lb P < Wb P) :
    thetaLStar P = (Wb P - Lb P) /
      (Real.sqrt ((1 / P.a + 3 / P.b - 1 / 2 * Lb P) ^ 2 + 6 / P.a * (Wb P - Lb P))
        + 1 / P.a + 3 / P.b - 1 / 2 * Lb P) := by
  obtain ⟨ha, hb, -, -, -, -, -⟩ := hP
  unfold thetaLStar
  have hd0 : 0 < Wb P - Lb P := by linarith
  have hA : 1 + 3 * P.a / P.b - P.a / 2 * Lb P = P.a * (1 / P.a + 3 / P.b - 1 / 2 * Lb P) := by
    field_simp
  have hden : ∀ s : ℝ, s + 1 / P.a + 3 / P.b - 1 / 2 * Lb P
      = s + (1 / P.a + 3 / P.b - 1 / 2 * Lb P) := fun s => by ring
  rw [hden, hA]
  have := aaa_aux P.a (1 / P.a + 3 / P.b - 1 / 2 * Lb P) (Wb P - Lb P) ha hd0
  rw [← this]
