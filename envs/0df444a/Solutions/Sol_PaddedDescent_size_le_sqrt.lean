-- Prove2me | solution 1 for PaddedDescent.size_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:40:57.336449+00:00
-- url     : https://prove2.me/submissions/921b7c0d-e8ff-4605-a627-cac5adfe90dd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_Threshold

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution (n : ℕ) : Nat.size n ≤ 2 * Nat.sqrt n + 2 := by
  rcases Nat.eq_zero_or_pos (Nat.size n) with h | h
  · omega
  obtain ⟨m, hm⟩ : ∃ m, Nat.size n = m + 1 := ⟨Nat.size n - 1, by omega⟩
  have h1 : 2 ^ m ≤ n := Nat.lt_size.1 (by omega)
  have h2 : 2 ^ (m / 2) ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt, ← pow_add]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h1
  have h3 : m / 2 < 2 ^ (m / 2) := Nat.lt_two_pow_self
  omega
end PaddedDescent
