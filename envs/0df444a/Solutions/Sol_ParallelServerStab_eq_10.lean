-- Prove2me | solution 1 for ParallelServerStab.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:32:39.608737+00:00
-- url     : https://prove2.me/submissions/d1441371-b6ff-4433-800f-d979909e6ce9

import Mathlib
import Definitions.Def_ParallelServerStab_Vcr

open ParallelServerStab in
theorem solution (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp : 0 < p) :
    Vcr s p < 1 ↔ 1 - 1 / (s : ℝ) < p := by
  have hS : (2:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have ha : 0 < (s:ℝ) - 1 := by linarith
  have hSp : 0 < (s:ℝ) := by linarith
  have hy : 0 < ((s:ℝ) + 1) / ((s:ℝ) - 1) := div_pos (by linarith) ha
  have e1 : Vcr s p < 1 ↔
      Real.sqrt (1 + 4 / (p * ((s:ℝ) - 1))) < ((s:ℝ) + 1) / ((s:ℝ) - 1) := by
    unfold Vcr
    rw [show ((s:ℝ) - 1) / (2 * (s:ℝ)) * (1 + Real.sqrt (1 + 4 / (p * ((s:ℝ) - 1)))) =
        (((s:ℝ) - 1) * (1 + Real.sqrt (1 + 4 / (p * ((s:ℝ) - 1))))) / (2 * (s:ℝ)) by ring,
      div_lt_one (by linarith), lt_div_iff₀ ha]
    constructor <;> intro h <;> nlinarith
  have e2 := Real.sqrt_lt' (x := 1 + 4 / (p * ((s:ℝ) - 1))) hy
  have e3 : 1 + 4 / (p * ((s:ℝ) - 1)) < (((s:ℝ) + 1) / ((s:ℝ) - 1)) ^ 2 ↔
      (s:ℝ) - 1 < p * (s:ℝ) := by
    have hd : 0 < p * ((s:ℝ) - 1) ^ 2 := mul_pos hp (pow_pos ha 2)
    have hk : (((s:ℝ) + 1) / ((s:ℝ) - 1)) ^ 2 - (1 + 4 / (p * ((s:ℝ) - 1))) =
        4 * (p * (s:ℝ) - ((s:ℝ) - 1)) / (p * ((s:ℝ) - 1) ^ 2) := by
      field_simp <;> ring
    rw [← sub_pos, hk, div_pos_iff_of_pos_right hd]
    constructor <;> intro h <;> linarith
  have e4 : (s:ℝ) - 1 < p * (s:ℝ) ↔ 1 - 1 / (s:ℝ) < p := by
    rw [show (1:ℝ) - 1 / (s:ℝ) = ((s:ℝ) - 1) / (s:ℝ) by rw [sub_div, div_self hSp.ne'],
      div_lt_iff₀ hSp]
  exact e1.trans (e2.trans (e3.trans e4))
