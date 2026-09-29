-- Prove2me | solution 1 for RobustMeanCov.TwoPoint.lemma1Quad_eq_of_chord
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:55:35.734948+00:00
-- url     : https://prove2.me/submissions/b454ffdf-64e0-47c0-87bf-7d44872c8b93

import Mathlib
import Definitions.Def_RobustMeanCov_TwoPoint_Lemma1Quadratic

open RobustMeanCov.TwoPoint

theorem solution (u : ℝ → ℝ) (a b qa qb : ℝ) (hab : a < b)
    (hchord : (u b - u a) / (b - a) = (qa + qb) / 2) :
    lemma1Quad u a b qa qb a = u a ∧ lemma1Quad u a b qa qb b = u b := by
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hc : 2 * (u b - u a) = (b - a) * (qa + qb) := by
    field_simp at hchord
    linarith
  have hca : a * (2 * (u b - u a)) = a * ((b - a) * (qa + qb)) := by rw [hc]
  have hcb : b * (2 * (u b - u a)) = b * ((b - a) * (qa + qb)) := by rw [hc]
  constructor
  · simp only [lemma1Quad, lemma1A, lemma1B, lemma1C]
    field_simp
    linarith [hca, hcb]
  · simp only [lemma1Quad, lemma1A, lemma1B, lemma1C]
    field_simp
    linarith [hca, hcb]
