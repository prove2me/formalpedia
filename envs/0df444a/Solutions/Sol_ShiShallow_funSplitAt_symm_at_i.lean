-- Prove2me | solution 1 for ShiShallow.funSplitAt_symm_at_i
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:35:43.710527+00:00
-- url     : https://prove2.me/submissions/dac6d8d2-10a0-4813-bc25-d95df2811ef8

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

theorem solution {n : ℕ} (i : Fin n) (a : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) :
    (Equiv.funSplitAt i Bool).symm (a, r) i = a := by
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

end
