-- Prove2me | solution 1 for ShiShallow.acceptProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:42:11.511676+00:00
-- url     : https://prove2.me/submissions/28d04366-ce1c-4ff7-b635-201cc5291f61

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the target theorem is renamed to `solution`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit

section
open ShiShallow

theorem solution {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    0 ≤ acceptProb c x out := by
  refine Finset.sum_nonneg fun y _ => ?_
  split
  · positivity
  · exact le_refl 0

end
