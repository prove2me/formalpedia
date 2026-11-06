-- Prove2me | solution 1 for SatFree.noBits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:12.124237+00:00
-- url     : https://prove2.me/submissions/471b8d9f-ecd3-4194-b1a6-622053e11dfd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Random

set_option autoImplicit false
section
section
open SatFree
open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution (M : TM2ComputableAux Bool Bool) (x : List Bool) (b : Bool) (t : ℕ)
    (ev : Nonempty (TM2OutputsInTime M.tm (x.map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)) :
    (∀ w : Fin 0 → Bool, ∃ b : Bool, Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)) ∧
    (1 - (0 : ℝ)) * (2 : ℝ) ^ 0 ≤ (Nat.card {w : Fin 0 → Bool //
      Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)} : ℝ) := by
  have e : ∀ w : Fin 0 → Bool, x ++ List.ofFn w = x := fun w => by simp
  have h : ∀ w : Fin 0 → Bool, Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t) :=
    fun w => by rw [e w]; exact ev
  refine ⟨fun w => ⟨b, h w⟩, ?_⟩
  have : Nonempty {w : Fin 0 → Bool //
      Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)} := ⟨⟨fun i => i.elim0, h _⟩⟩
  have h1 : 1 ≤ Nat.card {w : Fin 0 → Bool //
      Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)} := Nat.card_pos
  have h2 : (1 : ℝ) ≤ (Nat.card {w : Fin 0 → Bool //
      Nonempty (TM2OutputsInTime M.tm ((x ++ List.ofFn w).map M.inputAlphabet.invFun) (some ([b].map M.outputAlphabet.invFun)) t)} : ℝ) := by exact_mod_cast h1
  simpa using h2
end SatFree
