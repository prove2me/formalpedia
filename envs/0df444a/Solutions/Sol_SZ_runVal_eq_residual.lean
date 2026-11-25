-- Prove2me | solution 1 for SZ.runVal_eq_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:57:23.412975+00:00
-- url     : https://prove2.me/submissions/f0b73577-4e07-46ed-afe5-300f29b0fd36

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_valS_stepS
import Theorems.Thm_SZ_runState_succ
import Theorems.Thm_SZ_digitSum_succ
import Theorems.Thm_SZ_digitSum_zero


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (d : ℕ → ℤ × ℤ) (k : ℕ) :
    valS (runState (-12, 9) d k) = 3 ^ (k + 1) * ((3 * Real.sqrt 3 - 4)
      - digitSum 3 (fun i => (d i).1) k
      - Real.sqrt 3 * digitSum 3 (fun i => (d i).2) k) := by
  induction k with
  | zero =>
    rw [show runState ((-12 : ℤ), (9 : ℤ)) d 0 = ((-12 : ℤ), (9 : ℤ)) from rfl, valS,
      digitSum_zero, digitSum_zero]
    push_cast
    ring
  | succ k ih =>
    rw [runState_succ, valS_stepS, ih]
    simp only [digitSum_succ]
    have h3 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h3, valS]
    have hne : (3 : ℝ) ^ (k + 1) ≠ 0 := by positivity
    field_simp
    ring
end SZ
