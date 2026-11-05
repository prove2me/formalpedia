-- Prove2me | solution 1 for VariableBound.SmallBias.half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:05:14.64785+00:00
-- url     : https://prove2.me/submissions/9ca94190-1162-434a-ba0d-2be268f94752

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
import Theorems.Thm_VariableBound_SmallBias_ip_le_half

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (E : Fin m) :
    2 * #{p : F × F | ip (bits (p.1 ^ E.val)) (bits p.2) = 1} ≤ Fintype.card F ^ 2 := by
  rw [card_pairs, mul_sum]
  calc ∑ u₃ : F, 2 * #{u₄ : F | ip (bits (u₃ ^ E.val)) (bits u₄) = 1} ≤ ∑ _u₃ : F, Fintype.card F := sum_le_sum fun u₃ _ => ip_le_half bits _
    _ = Fintype.card F ^ 2 := by rw [sum_const, card_univ, smul_eq_mul, sq]
end VariableBound.SmallBias
