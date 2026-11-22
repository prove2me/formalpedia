-- Prove2me | solution 1 for ShiShallow.update_funSplitAt_symm
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:36:51.764978+00:00
-- url     : https://prove2.me/submissions/48e8fb33-c9b2-4b02-b612-787112aa2626

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

theorem solution {n : ℕ} (i : Fin n) (a b : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) :
    Function.update ((Equiv.funSplitAt i Bool).symm (a, r)) i b
      = (Equiv.funSplitAt i Bool).symm (b, r) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  · simp [Function.update_of_ne hj, Equiv.funSplitAt, Equiv.piSplitAt, dif_neg hj]

end
