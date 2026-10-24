-- Prove2me | solution 1 for ToricFoliations.divisor_intersection_le_one
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:18:10.353862+00:00
-- url     : https://prove2.me/submissions/ac53460f-e7c6-4a7d-bda8-4acb61a94f87

import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_ToricFoliations
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open ToricFoliations

theorem solution {n : ℕ} (C : WallData n) :
    ∀ i : Fin (n + 1), divisorIntersection C i ≤ 1 := by
  intro i
  have hmw : (0 : ℚ) ≤ C.mWall := by positivity
  have hms : (0 : ℚ) < C.mSigma := by exact_mod_cast C.mSigma_pos
  have hms' : (0 : ℚ) < C.mSigma' := by exact_mod_cast C.mSigma'_pos
  have hwall : (C.mWall : ℚ) ≤ C.mSigma := by
    exact_mod_cast Nat.le_of_dvd C.mSigma_pos C.wall_dvd_sigma
  have hwall' : (C.mWall : ℚ) ≤ C.mSigma' := by
    exact_mod_cast Nat.le_of_dvd C.mSigma'_pos C.wall_dvd_sigma'
  have ha : (0 : ℚ) < C.a (wallIndex n C.hn) := by exact_mod_cast C.an_pos
  unfold divisorIntersection
  split_ifs with hi
  · exact (div_le_one hms').mpr hwall'
  · have hii : i.val ≤ (wallIndex n C.hn).val := by
      have hilast : i.val ≠ n := by
        intro heq
        apply hi
        apply Fin.ext
        exact heq
      have hib := i.isLt
      simp only [wallIndex]
      omega
    have hai : (C.a i : ℚ) ≤ C.a (wallIndex n C.hn) := by
      exact_mod_cast C.sorted i (wallIndex n C.hn) hii
    apply (div_le_one (mul_pos ha hms)).mpr
    exact (mul_le_mul_of_nonneg_right hai hmw).trans
      (mul_le_mul_of_nonneg_left hwall ha.le)

#print axioms solution

