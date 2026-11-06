-- Prove2me | solution 1 for Printed.absorb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:11:15.593213+00:00
-- url     : https://prove2.me/submissions/e730a39b-7142-4a2f-a9d7-9de26fe2d329

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_Printed_Absorb

set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution (a k : ℕ) : ∃ Cc : ℕ, a ≤ Cc ∧ ∀ x : ℕ, 1 ≤ x → k * x + a * (k * x) ^ a ≤ Cc * x ^ Cc := by
  refine ⟨k + a * k ^ a + a + 1, by omega, fun x hx => ?_⟩
  have h1 : x ≤ x ^ (k + a * k ^ a + a + 1) := Nat.le_self_pow (by omega) x
  have h2 : x ^ a ≤ x ^ (k + a * k ^ a + a + 1) := Nat.pow_le_pow_right hx (by omega)
  calc k * x + a * (k * x) ^ a = k * x + a * k ^ a * x ^ a := by rw [mul_pow]; ring
    _ ≤ k * x ^ (k + a * k ^ a + a + 1) + a * k ^ a * x ^ (k + a * k ^ a + a + 1) := Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (k + a * k ^ a) * x ^ (k + a * k ^ a + a + 1) := by ring
    _ ≤ (k + a * k ^ a + a + 1) * x ^ (k + a * k ^ a + a + 1) := Nat.mul_le_mul_right _ (by omega)
end Printed
