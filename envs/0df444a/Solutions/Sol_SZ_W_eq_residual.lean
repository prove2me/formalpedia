-- Prove2me | solution 1 for SZ.W_eq_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:09.503082+00:00
-- url     : https://prove2.me/submissions/d92409f9-851d-4f3f-ba02-c870bc72b7e9

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_W_zero
import Theorems.Thm_SZ_W_succ
import Theorems.Thm_SZ_digitSum_succ
import Theorems.Thm_SZ_digitSum_zero


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) :
    W k = 3 ^ (k + 1) * ((3 * Real.sqrt 3 - 4) - digitSum 3 digitA k
      - Real.sqrt 3 * digitSum 3 digitB k) := by
  induction k with
  | zero => rw [W_zero, digitSum_zero, digitSum_zero]; ring
  | succ k ih =>
    rw [W_succ, ih, digitSum_succ, digitSum_succ]
    have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3]
    have hne : (3 : ℝ) ^ (k + 1) ≠ 0 := by positivity
    field_simp
    ring
end SZ
