-- Prove2me | solution 1 for SplitCount.poly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:27:37.90802+00:00
-- url     : https://prove2.me/submissions/8c308638-01a7-414b-8d6c-5148c1fee6bc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitCount_Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_SplitCount_Sizes

set_option autoImplicit false
section
section
open SplitCount
open Groundwork Groundwork.Prog CountKSat
namespace SplitCount
theorem _root_.solution {s A B P d e x : ℕ} (hs : 1 ≤ s) (hx : x ≤ B * s ^ d + A * (P * s ^ e) ^ A) :
    x ≤ (B + d + A * P ^ A + e * A) * s ^ (B + d + A * P ^ A + e * A) := by
  obtain ⟨c, hc⟩ : ∃ c, c = B + d + A * P ^ A + e * A := ⟨_, rfl⟩
  rw [← hc]
  have h1 : s ^ d ≤ s ^ c := Nat.pow_le_pow_right hs (by omega)
  have h2 : s ^ (e * A) ≤ s ^ c := Nat.pow_le_pow_right hs (by omega)
  calc x ≤ B * s ^ d + A * (P * s ^ e) ^ A := hx
    _ = B * s ^ d + A * P ^ A * s ^ (e * A) := by rw [mul_pow, ← pow_mul, mul_assoc]
    _ ≤ B * s ^ c + A * P ^ A * s ^ c := Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (B + A * P ^ A) * s ^ c := by ring
    _ ≤ c * s ^ c := Nat.mul_le_mul_right _ (by omega)
end SplitCount
