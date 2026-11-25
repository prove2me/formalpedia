-- Prove2me | solution 1 for SZ.W_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:13:25.399801+00:00
-- url     : https://prove2.me/submissions/65ea31f9-255b-45b6-88d2-efd813d06703

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_pick_residual_mem
import Theorems.Thm_SZ_W_zero
import Theorems.Thm_SZ_W_succ
section
namespace SZ
open Filter Topology
private theorem s3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
private theorem s3_ub : Real.sqrt 3 < 1.8 := by
  have h : Real.sqrt 3 < Real.sqrt (1.8 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.8)] at h
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (k : ℕ) : 0 ≤ W k ∧ W k ≤ 3 + 3 * Real.sqrt 3 := by
  induction k with
  | zero =>
    rw [W_zero]
    constructor <;> linarith [s3_lb, s3_ub]
  | succ k ih =>
    obtain ⟨hlo, hhi⟩ := pick_residual_mem ih.1 ih.2
    rw [W_succ, digitA, digitB]
    constructor <;> linarith
end SZ
