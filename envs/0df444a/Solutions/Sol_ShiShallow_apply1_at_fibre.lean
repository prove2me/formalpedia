-- Prove2me | solution 1 for ShiShallow.apply1_at_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:14:44.899576+00:00
-- url     : https://prove2.me/submissions/e6218f14-642a-4cec-9a92-29cdb6a0a192

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
import Theorems.Thm_ShiShallow_funSplitAt_symm_at_i
import Theorems.Thm_ShiShallow_update_funSplitAt_symm

section
open ShiShallow

theorem solution {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n)
    (a : Bool) (r : {j : Fin n // j ≠ i} → Bool) :
    apply1 U i ψ ((Equiv.funSplitAt i Bool).symm (a, r))
      = ∑ b : Bool, U a b * ψ ((Equiv.funSplitAt i Bool).symm (b, r)) := by
  unfold apply1
  rw [funSplitAt_symm_at_i]
  exact Finset.sum_congr rfl (fun b _ => by rw [update_funSplitAt_symm])

end
