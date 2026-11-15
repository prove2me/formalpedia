-- Prove2me | solution 1 for QuantumLTF.Membership.strict_orientation_sign
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:00:19.608234+00:00
-- url     : https://prove2.me/submissions/0a64bae5-76a8-4257-b40f-52e99a288f84

import Mathlib
import Definitions.Def_QuantumLTF_Membership_sgn

open QuantumLTF.Membership

theorem solution (a h L : ℝ) (ha : a ≠ 0) (hh : |h| ≤ L) :
    (if sgn (a * ((L + 1) - h)) = 1 ∧
        sgn (a * (-(L + 1) - h)) = -1 then 1 else -1) =
      sgn a := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hh1 : -L ≤ h := (abs_le.mp hh).1
    have hh2 : h ≤ L := (abs_le.mp hh).2
    simp only [sgn]
    have hr : a * ((L + 1) - h) < 0 := mul_neg_of_neg_of_pos ha (by linarith)
    have hl : 0 < a * (-(L + 1) - h) := mul_pos_of_neg_of_neg ha (by linarith)
    simp [if_neg (not_le.mpr hr), if_pos hl.le, if_neg (not_le.mpr ha)]
  · have hh1 : -L ≤ h := (abs_le.mp hh).1
    have hh2 : h ≤ L := (abs_le.mp hh).2
    simp only [sgn]
    have hr : 0 < a * ((L + 1) - h) := mul_pos ha (by linarith)
    have hl : a * (-(L + 1) - h) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
    have hl' : a * (-1 + -L - h) < 0 := by convert hl using 1 <;> ring
    simp [if_pos hr.le, if_neg (not_le.mpr hl'), if_pos ha.le]
