-- Prove2me | solution 1 for ShiShallow.IsLocal.conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:55:40.35758+00:00
-- url     : https://prove2.me/submissions/f577d0f8-a58c-40a2-ba23-e0101d3fb5f5

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
import Definitions.Def_ShiShallow_Operator

section
open ShiShallow

theorem solution {n : ℕ} {S : Finset (Fin n)} {A : Op n} (h : IsLocal S A) :
    IsLocal S A.conjTranspose := by
  constructor
  · intro y z hne
    rw [Matrix.conjTranspose_apply, h.vanish (fun hc => hne (fun k hk => (hc k hk).symm)),
      star_zero]
  · intro y z y' z' hy hz hyz hyz'
    rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply,
      h.entry_congr hz hy (fun k hk => (hyz k hk).symm) (fun k hk => (hyz' k hk).symm)]

end
