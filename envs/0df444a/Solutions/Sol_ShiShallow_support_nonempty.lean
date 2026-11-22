-- Prove2me | solution 1 for ShiShallow.support_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:28:19.055308+00:00
-- url     : https://prove2.me/submissions/ef8d9581-3321-4e40-b2bc-9b3c13d5dbda

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

theorem solution {n : ℕ} (g : Instr n) : g.support.Nonempty := by
  cases g with
  | h i => exact ⟨i, by simp [Instr.support]⟩
  | s i => exact ⟨i, by simp [Instr.support]⟩
  | t i => exact ⟨i, by simp [Instr.support]⟩
  | cnot i j _ => exact ⟨i, by simp [Instr.support]⟩

end
