-- Prove2me | solution 1 for Wrap.Arith.poly_part_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:18:21.920729+00:00
-- url     : https://prove2.me/submissions/d3ce52bb-a864-4f69-a8ed-a08fe5723d34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Wrap_Arith

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution (C a d : ℕ) {n L X : ℕ} (hL : L ≤ a * (n + 2) ^ d) (hX : X ≤ a * (n + 2) ^ d) :
    C * L ^ C + X + 1 ≤ (C * a ^ C + a + 1) * (n + 2) ^ (d * C + d) := by
  have hb : 1 ≤ n + 2 := by omega
  have h1 : L ^ C ≤ a ^ C * (n + 2) ^ (d * C + d) := by
    calc L ^ C ≤ (a * (n + 2) ^ d) ^ C := Nat.pow_le_pow_left hL C
      _ = a ^ C * (n + 2) ^ (d * C) := by rw [mul_pow, ← pow_mul]
      _ ≤ a ^ C * (n + 2) ^ (d * C + d) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (Nat.le_add_right _ _))
  have h2 : X ≤ a * (n + 2) ^ (d * C + d) := hX.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (Nat.le_add_left _ _)))
  have h3 : 1 ≤ (n + 2) ^ (d * C + d) := Nat.one_le_pow _ _ (by omega)
  calc C * L ^ C + X + 1 ≤ C * (a ^ C * (n + 2) ^ (d * C + d)) + a * (n + 2) ^ (d * C + d) + (n + 2) ^ (d * C + d) :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2) h3
    _ = (C * a ^ C + a + 1) * (n + 2) ^ (d * C + d) := by ring
end Wrap.Arith
