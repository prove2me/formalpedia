-- Prove2me | solution 1 for VariableBound.SmallBias.small_bias
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:03:37.522586+00:00
-- url     : https://prove2.me/submissions/a11e4dbc-bd99-4089-9674-24baf4580fac

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
import Theorems.Thm_VariableBound_SmallBias_card_eq
import Theorems.Thm_VariableBound_SmallBias_small_bias_count

set_option autoImplicit false
section
section
open VariableBound VariableBound.SmallBias
open Finset AppVariables
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {m s : ℕ}
namespace VariableBound.SmallBias
theorem _root_.solution (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (h16 : 16 * m ≤ 2 ^ s) (V' : Finset (Fin m)) (hV : V'.Nonempty) :
    15 * Fintype.card F ^ 2 ≤ 32 * #{p : F × F | Odd #{E ∈ V' | ip (bits (p.1 ^ E.val)) (bits p.2) = 1}} := by
  have h1 := small_bias_count bits V' hV
  rw [← card_eq bits] at h16
  have h2 : 16 * ((m - 1) * Fintype.card F) ≤ Fintype.card F ^ 2 := by
    rw [sq, ← mul_assoc]
    exact Nat.mul_le_mul_right _ (le_trans (by omega) h16)
  omega
end VariableBound.SmallBias
