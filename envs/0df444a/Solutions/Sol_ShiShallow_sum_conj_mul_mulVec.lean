-- Prove2me | solution 1 for ShiShallow.sum_conj_mul_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:34:27.576863+00:00
-- url     : https://prove2.me/submissions/c58bade6-05a1-4923-9d80-4283ace62e9b

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the target theorem is renamed to `solution`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib

section

theorem solution {U : Matrix Bool Bool ℂ} (hU : U.conjTranspose * U = 1)
    (v : Bool → ℂ) :
    ∑ a : Bool, (starRingEnd ℂ) (∑ b : Bool, U a b * v b) * (∑ b : Bool, U a b * v b)
      = ∑ b : Bool, (starRingEnd ℂ) (v b) * v b := by
  have e00 := congrFun (congrFun hU false) false
  have e01 := congrFun (congrFun hU false) true
  have e10 := congrFun (congrFun hU true) false
  have e11 := congrFun (congrFun hU true) true
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
             Fintype.sum_bool] at e00 e01 e10 e11
  norm_num at e00 e01 e10 e11
  -- `norm_num` leaves the hypotheses in `starRingEnd` form; keep the goal in the same
  -- form so `ring` sees one atom per conjugated entry rather than `star` and
  -- `starRingEnd` as unrelated symbols.
  simp only [Fintype.sum_bool, map_add, map_mul]
  linear_combination ((starRingEnd ℂ) (v false) * v false) * e00
    + ((starRingEnd ℂ) (v false) * v true) * e01
    + ((starRingEnd ℂ) (v true) * v false) * e10
    + ((starRingEnd ℂ) (v true) * v true) * e11

end
