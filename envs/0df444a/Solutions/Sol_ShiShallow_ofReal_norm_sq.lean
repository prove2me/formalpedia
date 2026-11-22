-- Prove2me | solution 1 for ShiShallow.ofReal_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:03:25.78214+00:00
-- url     : https://prove2.me/submissions/73dc5ad6-69ba-43a2-be81-736aa93ed32a

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

theorem solution (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  rw [Complex.sq_norm, mul_comm]
  exact (Complex.mul_conj z).symm

end
