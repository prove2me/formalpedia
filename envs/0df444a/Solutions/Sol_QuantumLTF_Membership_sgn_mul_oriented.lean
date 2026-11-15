-- Prove2me | solution 1 for QuantumLTF.Membership.sgn_mul_oriented
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:19:51.850227+00:00
-- url     : https://prove2.me/submissions/688461a2-88b8-4353-ab65-fc9f9b3cfda2

import Mathlib
import Definitions.Def_QuantumLTF_Membership_sgn

open QuantumLTF.Membership

theorem solution (a x : ℝ) (ha : a ≠ 0) :
    (if sgn a = 1 then sgn (a * x) = sgn x
     else sgn (a * x) = sgn (-x)) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hsa : sgn a ≠ 1 := by simp [sgn, not_le.mpr ha]
    rw [if_neg hsa]
    by_cases hx : x = 0
    · subst x
      simp [sgn]
    · rcases lt_or_gt_of_ne hx with hx | hx
      · have hp : 0 < a * x := mul_pos_of_neg_of_neg ha hx
        have hn : 0 < -x := neg_pos.mpr hx
        simp [sgn, hp.le, hn.le]
      · have hp : a * x < 0 := mul_neg_of_neg_of_pos ha hx
        have hn : -x < 0 := by linarith
        simp [sgn, not_le.mpr hp, not_le.mpr hn]
  · have hsa : sgn a = 1 := by simp [sgn, ha.le]
    rw [if_pos hsa]
    by_cases hx : 0 ≤ x
    · have hp : 0 ≤ a * x := mul_nonneg ha.le hx
      simp [sgn, hp, hx]
    · have hx' : x < 0 := not_le.mp hx
      have hp : a * x < 0 := mul_neg_of_pos_of_neg ha hx'
      simp [sgn, not_le.mpr hp, hx]
