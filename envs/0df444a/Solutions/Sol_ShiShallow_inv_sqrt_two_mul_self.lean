-- Prove2me | solution 1 for ShiShallow.inv_sqrt_two_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:37:41.963724+00:00
-- url     : https://prove2.me/submissions/0498433f-cf64-4da5-bbbf-1e5a7092985b

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

theorem solution : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [one_div]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hr]
  push_cast
  ring

end
