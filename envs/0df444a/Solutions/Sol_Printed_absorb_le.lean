-- Prove2me | solution 1 for Printed.absorb_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:14:30.529926+00:00
-- url     : https://prove2.me/submissions/81e63470-933d-4e0a-9f1e-d04e33622817

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Definitions.Def_Printed_Absorb
import Theorems.Thm_Printed_absorb

set_option autoImplicit false
section
section
open Printed
namespace Printed
theorem _root_.solution (a k : ℕ) : ∃ Cc : ℕ, a ≤ Cc ∧ ∀ x s y : ℕ, 1 ≤ x → s ≤ k * x → y ≤ k * x → s + a * y ^ a ≤ Cc * x ^ Cc := by
  obtain ⟨Cc, h1, h2⟩ := absorb a k
  exact ⟨Cc, h1, fun x s y hx hs hy => (Nat.add_le_add hs (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy _))).trans (h2 x hx)⟩
end Printed
