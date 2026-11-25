-- Prove2me | solution 1 for SZ.branchDigit_adm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:49:22.336188+00:00
-- url     : https://prove2.me/submissions/fe8ab420-3b22-4478-9e1b-2e2adbee87d3

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
section
namespace SZ
open Filter Topology
private theorem t3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
private theorem t3_ub : Real.sqrt 3 < 1.8 := by
  have h : Real.sqrt 3 < Real.sqrt (1.8 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.8)] at h
private theorem valS_00 : valS ((0 : ℤ), (0 : ℤ)) = 0 := by norm_num [valS]
private theorem valS_20 : valS ((2 : ℤ), (0 : ℤ)) = 2 := by norm_num [valS]
private theorem valS_02 : valS ((0 : ℤ), (2 : ℤ)) = 2 * Real.sqrt 3 := by norm_num [valS]
private theorem valS_22 : valS ((2 : ℤ), (2 : ℤ)) = 2 + 2 * Real.sqrt 3 := by norm_num [valS]
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {w : ℝ} (h : InO w) (b : Bool) :
    0 ≤ w - valS (branchDigit w b) ∧ w - valS (branchDigit w b) ≤ 1 + Real.sqrt 3 := by
  have e1 : w ≤ 1 + Real.sqrt 3 → branchDigit w b = cond b (2, 0) (0, 0) := by
    intro hw; unfold branchDigit; rw [if_pos hw]
  have e2 : ¬ (w ≤ 1 + Real.sqrt 3) → w ≤ 3 + Real.sqrt 3 →
      branchDigit w b = cond b (2, 0) (0, 2) := by
    intro h1 h2; unfold branchDigit; rw [if_neg h1, if_pos h2]
  have e3 : ¬ (w ≤ 1 + Real.sqrt 3) → ¬ (w ≤ 3 + Real.sqrt 3) →
      branchDigit w b = cond b (2, 2) (0, 2) := by
    intro h1 h2; unfold branchDigit; rw [if_neg h1, if_neg h2]
  rcases h with hx | hx | hx
  · rw [e1 hx.2]
    cases b <;> simp only [Bool.cond_true, Bool.cond_false, valS_00, valS_20] <;>
      constructor <;> linarith [t3_lb, t3_ub, hx.1, hx.2]
  · have h1 : ¬ (w ≤ 1 + Real.sqrt 3) := by push Not; linarith [t3_lb, hx.1]
    rw [e2 h1 hx.2]
    cases b <;> simp only [Bool.cond_true, Bool.cond_false, valS_02, valS_20] <;>
      constructor <;> linarith [t3_lb, t3_ub, hx.1, hx.2]
  · have h1 : ¬ (w ≤ 1 + Real.sqrt 3) := by push Not; linarith [t3_lb, hx.1]
    have h2 : ¬ (w ≤ 3 + Real.sqrt 3) := by push Not; linarith [t3_lb, hx.1]
    rw [e3 h1 h2]
    cases b <;> simp only [Bool.cond_true, Bool.cond_false, valS_02, valS_22] <;>
      constructor <;> linarith [t3_lb, t3_ub, hx.1, hx.2]
end SZ
