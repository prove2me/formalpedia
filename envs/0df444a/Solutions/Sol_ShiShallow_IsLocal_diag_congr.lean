-- Prove2me | solution 1 for ShiShallow.IsLocal.diag_congr
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:44:52.229391+00:00
-- url     : https://prove2.me/submissions/9f3763a1-1c97-48f7-929f-136d3a6547ea

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

theorem solution {n : ℕ} {S : Finset (Fin n)} {A : Op n} (h : IsLocal S A)
    {x x' : Bits n} (hx : ∀ k ∈ S, x k = x' k) : A x x = A x' x' := h.entry_congr hx hx (fun _ _ => rfl) (fun _ _ => rfl)

end
