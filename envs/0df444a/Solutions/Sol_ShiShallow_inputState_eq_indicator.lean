-- Prove2me | solution 1 for ShiShallow.inputState_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T05:27:29.263546+00:00
-- url     : https://prove2.me/submissions/b60dc691-b12f-4730-9480-43b86e6414b9

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
import Theorems.Thm_ShiShallow_padIn_castAdd
import Theorems.Thm_ShiShallow_padIn_natAdd

section
open ShiShallow

theorem solution {n m : ℕ} (x : Bits n) (y : Bits (n + m)) :
    inputState (m := m) x y = if y = padIn x then 1 else 0 := by
  have hiff : ((∀ i : Fin n, y (Fin.castAdd m i) = x i) ∧
      (∀ k : Fin m, y (Fin.natAdd n k) = false)) ↔ y = padIn x := by
    constructor
    · rintro ⟨h1, h2⟩
      funext k
      refine Fin.addCases (motive := fun k => y k = padIn (m := m) x k) ?_ ?_ k
      · intro i; rw [padIn_castAdd]; exact h1 i
      · intro j; rw [padIn_natAdd]; exact h2 j
    · rintro rfl
      exact ⟨fun i => padIn_castAdd x i, fun j => padIn_natAdd x j⟩
  unfold inputState
  simp only [hiff]

end
