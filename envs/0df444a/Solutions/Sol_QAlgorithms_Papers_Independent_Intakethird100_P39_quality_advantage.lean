-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P39.quality_advantage
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:37:34.524764+00:00
-- url     : https://prove2.me/submissions/b240addd-c7ce-4049-a419-e9af4f3ee83d

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P39

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intakethird100.P39 in
theorem solution (r rprime : ℕ) (hr : rprime ≤ r)
    (F2 Fm tau2 taum TR : ℝ)
    (hF2 : F2 ∈ Set.Icc (-1) 1) (hFm : Fm ∈ Set.Icc (-1) 1) (hTR : 0 < TR)
    (htau2 : 0 ≤ tau2) (htaum : 0 ≤ taum) :
    (Fm > F2 ^ r * Real.exp (-((rprime : ℝ) * tau2 - taum) / TR) ↔
      quality Fm taum TR > quality (F2 ^ r) ((rprime : ℝ) * tau2) TR) ∧
    (quality Fm 0 TR > quality (F2 ^ r) 0 TR ↔ Fm > F2 ^ r) := by
  have hE : Real.exp (-((rprime : ℝ) * tau2 - taum) / TR) * Real.exp (-taum / TR)
      = Real.exp (-((rprime : ℝ) * tau2) / TR) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpos := Real.exp_pos (-taum / TR)
  constructor
  · unfold quality
    constructor
    · intro h
      have := mul_lt_mul_of_pos_right h hpos
      rw [mul_assoc, hE] at this
      linarith
    · intro h
      by_contra hc
      push_neg at hc
      have := mul_le_mul_of_nonneg_right hc hpos.le
      rw [mul_assoc, hE] at this
      linarith
  · simp [quality]
