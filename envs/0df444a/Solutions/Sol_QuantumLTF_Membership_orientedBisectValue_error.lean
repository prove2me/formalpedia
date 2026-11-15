-- Prove2me | solution 1 for QuantumLTF.Membership.orientedBisectValue_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:10:24.624191+00:00
-- url     : https://prove2.me/submissions/71cff47f-954b-4d25-8a16-8a4e609662bb

import Mathlib
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue

open QuantumLTF.Membership

theorem solution (s : ℤ) (q : ℕ) (lo hi h : ℝ)
    (hlo : lo ≤ h) (hhi : h ≤ hi) :
    |orientedBisectValue s q lo hi h - h| ≤
      (hi - lo) / (2 : ℝ) ^ (q + 1) := by
  induction q generalizing lo hi with
  | zero =>
      simp only [orientedBisectValue, pow_one]
      rw [abs_le]
      constructor <;> linarith
  | succ q ih =>
      let mid := (lo + hi) / 2
      have hwL : (mid - lo) / (2 : ℝ) ^ (q + 1) =
          (hi - lo) / (2 : ℝ) ^ (q + 2) := by
        dsimp [mid]
        rw [pow_succ]
        ring
      have hwR : (hi - mid) / (2 : ℝ) ^ (q + 1) =
          (hi - lo) / (2 : ℝ) ^ (q + 2) := by
        dsimp [mid]
        rw [pow_succ]
        ring
      simp only [orientedBisectValue]
      split
      · by_cases hm : h ≤ mid
        · have hs : sgn (mid - h) = 1 := by simp [sgn, sub_nonneg.mpr hm]
          rw [hs, if_pos rfl]
          rw [← hwL]
          exact ih lo mid hlo hm
        · have hs : sgn (mid - h) = -1 := by
            simp [sgn, not_le.mp hm]
          rw [hs]
          norm_num
          rw [← hwR]
          exact ih mid hi (le_of_not_ge hm) hhi
      · by_cases hm : mid ≤ h
        · have hs : sgn (h - mid) = 1 := by simp [sgn, sub_nonneg.mpr hm]
          rw [hs, if_pos rfl]
          rw [← hwR]
          exact ih mid hi hm hhi
        · have hs : sgn (h - mid) = -1 := by
            simp [sgn, not_le.mp hm]
          rw [hs]
          norm_num
          rw [← hwL]
          exact ih lo mid hlo (le_of_not_ge hm)
