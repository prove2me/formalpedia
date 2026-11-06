-- Prove2me | solution 1 for Printed.absorb_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:11:23.859971+00:00
-- url     : https://prove2.me/submissions/4902b8cf-befc-4b8d-afda-8ef1a9f453ca

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
theorem _root_.solution {a Cc : ℕ} (h : a ≤ Cc) {p x : ℝ} (hp : 0 ≤ p) (hx : 1 ≤ x) : (a : ℝ) * p * x ^ a ≤ Cc * p * x ^ Cc := by
  have h1 : (a : ℝ) ≤ Cc := by exact_mod_cast h
  have h2 : x ^ a ≤ x ^ Cc := pow_le_pow_right₀ hx h
  have hx0 : 0 ≤ x := by linarith
  exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hp) h2 (pow_nonneg hx0 a) (mul_nonneg (Nat.cast_nonneg _) hp)
end Printed
