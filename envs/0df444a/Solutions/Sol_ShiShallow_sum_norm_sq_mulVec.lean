-- Prove2me | solution 1 for ShiShallow.sum_norm_sq_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:13:20.858987+00:00
-- url     : https://prove2.me/submissions/03316d52-a984-411d-8f51-c71dd6d42798

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
import Theorems.Thm_ShiShallow_sum_conj_mul_mulVec

section
open ShiShallow

theorem solution {U : Matrix Bool Bool ℂ} (hU : U.conjTranspose * U = 1)
    (v : Bool → ℂ) :
    ∑ a : Bool, ‖∑ b : Bool, U a b * v b‖ ^ 2 = ∑ b : Bool, ‖v b‖ ^ 2 := by
  have h := sum_conj_mul_mulVec hU v
  have hz : ∀ z : ℂ, (starRingEnd ℂ) z * z = (Complex.normSq z : ℂ) := by
    intro z; rw [mul_comm]; exact Complex.mul_conj z
  simp only [hz] at h
  simp only [Complex.sq_norm]
  exact_mod_cast h

end
