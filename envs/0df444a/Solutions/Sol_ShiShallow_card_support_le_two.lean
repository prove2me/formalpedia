-- Prove2me | solution 1 for ShiShallow.card_support_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-10T04:29:44.867008+00:00
-- url     : https://prove2.me/submissions/f613f264-7811-4311-bf2e-a88697b650d0

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

theorem solution {n : ℕ} (g : Instr n) : g.support.card ≤ 2 := by
  cases g with
  | h i => simp [Instr.support]
  | s i => simp [Instr.support]
  | t i => simp [Instr.support]
  | cnot i j _ =>
      simp only [Instr.support]
      exact (Finset.card_insert_le _ _).trans (by simp)

end
