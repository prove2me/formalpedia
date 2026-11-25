-- Prove2me | solution 1 for SZ.coverState_snd_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:28:05.560808+00:00
-- url     : https://prove2.me/submissions/9a0357c7-8547-453b-8e3f-1616f2c63c4e

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_coverState_succ
import Theorems.Thm_SZ_digitB_mem

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) : 6 * 3 ^ k + 3 ≤ (coverState k).2 := by
  induction k with
  | zero => norm_num [coverState]
  | succ k ih =>
    have hb : digitB k ≤ 2 := by rcases digitB_mem k with h | h <;> omega
    rw [coverState_succ]
    simp only
    have h3 : (3:ℤ) ^ (k + 1) = 3 * 3 ^ k := by ring
    omega
end SZ
