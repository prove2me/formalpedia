-- Prove2me | solution 1 for PaddedDescent.decay_aux_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:13:21.569195+00:00
-- url     : https://prove2.me/submissions/b8b8fe17-0c80-4252-aba7-148baad7220a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_SparsifyWidthK_Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_PaddedDescent_Choice
import Theorems.Thm_PaddedDescent_decay_step

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution {s : ℕ} (ih : 8963 ^ (19 * s / 3 + 700) * (2 ^ 10 * (s + 2 ^ 15) ^ 6 * 2 ^ s) ≤ 10000 ^ (19 * s / 3 + 700)) :
    8963 ^ (19 * (s + 3) / 3 + 700) * (2 ^ 10 * (s + 3 + 2 ^ 15) ^ 6 * 2 ^ (s + 3)) ≤ 10000 ^ (19 * (s + 3) / 3 + 700) := by
  have hs := decay_step s
  have e : 19 * (s + 3) / 3 + 700 = 19 * s / 3 + 700 + 19 := by omega
  rw [e, pow_add 8963 (19 * s / 3 + 700) 19, pow_add 10000 (19 * s / 3 + 700) 19]
  obtain ⟨t, ht⟩ : ∃ t, t = 19 * s / 3 + 700 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 8963 ^ 19 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 10000 ^ 19 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ 15 := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hM] at hs ⊢
  rw [← ht, ← hM] at ih
  rw [← ht]
  calc 8963 ^ t * A * (2 ^ 10 * (s + 3 + M) ^ 6 * 2 ^ (s + 3))
      = 8963 ^ t * (2 ^ 10 * 2 ^ s) * (A * (8 * (s + 3 + M) ^ 6)) := by ring
    _ ≤ 8963 ^ t * (2 ^ 10 * 2 ^ s) * (B * (s + M) ^ 6) := Nat.mul_le_mul_left _ hs
    _ = 8963 ^ t * (2 ^ 10 * (s + M) ^ 6 * 2 ^ s) * B := by ring
    _ ≤ 10000 ^ t * B := Nat.mul_le_mul_right _ ih
end PaddedDescent
