-- Prove2me | solution 1 for VariableBound.SmallBias.small_bias_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:02:53.266576+00:00
-- url     : https://prove2.me/submissions/11076549-db9f-4ce0-a2c6-63a0c543d6a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Family_SmallBias
import Theorems.Thm_VariableBound_SmallBias_card_pairs
import Theorems.Thm_VariableBound_SmallBias_odd_iff_ip
import Theorems.Thm_VariableBound_SmallBias_roots
import Theorems.Thm_VariableBound_SmallBias_ip_half

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (V' : Finset (Fin m)) (hV : V'.Nonempty) :
    Fintype.card F ^ 2 ≤ 2 * #{p : F × F | Odd #{E ∈ V' | ip (bits (p.1 ^ E.val)) (bits p.2) = 1}} + (m - 1) * Fintype.card F := by
  classical
  rw [card_pairs, mul_sum]
  have hterm : ∀ u₃ : F, Fintype.card F ≤ 2 * #{u₄ : F | Odd #{E ∈ V' | ip (bits (u₃ ^ E.val)) (bits u₄) = 1}} + if ∑ E ∈ V', u₃ ^ E.val = 0 then Fintype.card F else 0 := by
    intro u₃
    simp only [odd_iff_ip]
    split_ifs with h0
    · exact Nat.le_add_left _ _
    · exact (ip_half bits _ h0).ge
  calc Fintype.card F ^ 2 = ∑ _u₃ : F, Fintype.card F := by rw [sum_const, card_univ, smul_eq_mul, sq]
    _ ≤ ∑ u₃ : F, (2 * #{u₄ : F | Odd #{E ∈ V' | ip (bits (u₃ ^ E.val)) (bits u₄) = 1}} + if ∑ E ∈ V', u₃ ^ E.val = 0 then Fintype.card F else 0) := sum_le_sum fun u₃ _ => hterm u₃
    _ = ∑ u₃ : F, 2 * #{u₄ : F | Odd #{E ∈ V' | ip (bits (u₃ ^ E.val)) (bits u₄) = 1}} + #{u₃ : F | ∑ E ∈ V', u₃ ^ E.val = 0} * Fintype.card F := by
        rw [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ (roots V' hV)) _
end VariableBound.SmallBias
