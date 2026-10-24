-- Prove2me | solution 1 for SKAlgorithm.Qudit.eq_4
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:49:22.187696+00:00
-- url     : https://prove2.me/submissions/2aeff7cb-07dd-45bc-a396-aa9de072a402

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms SKAlgorithm.Qudit

namespace SKAlgorithm.Qudit.ClosedFormProof

lemma three_halves (x : ℝ) (hx : 0 < x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  calc
    x ^ ((3 : ℝ) / 2) = x ^ (1 + 1 / (2 : ℝ)) := by norm_num
    _ = x * Real.sqrt x := by rw [Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma normalization (c : ℝ) (hc : 0 < c) :
    c * (1 / c ^ 2) ^ ((3 : ℝ) / 2) = 1 / c ^ 2 := by
  rw [three_halves _ (by positivity), Real.sqrt_div (by norm_num), Real.sqrt_one,
    Real.sqrt_sq hc.le]
  field_simp

end SKAlgorithm.Qudit.ClosedFormProof

theorem solution (c ε₀ : ℝ) (hc : 0 < c) (hε₀ : 0 < ε₀) (n : ℕ) :
    epsSeq c ε₀ n = 1 / c ^ 2 * (ε₀ * c ^ 2) ^ (((3 : ℝ) / 2) ^ n) := by
  induction n with
  | zero =>
    simp only [epsSeq, Function.iterate_zero, id_eq, pow_zero, Real.rpow_one]
    field_simp
  | succ n ih =>
    have hstep : epsSeq c ε₀ (n + 1) = c * epsSeq c ε₀ n ^ ((3 : ℝ) / 2) :=
      Function.iterate_succ_apply' _ _ _
    rw [hstep, ih, Real.mul_rpow (by positivity) (by positivity), ← mul_assoc,
      ClosedFormProof.normalization c hc, ← Real.rpow_mul (by positivity)]
    simp only [pow_succ]
