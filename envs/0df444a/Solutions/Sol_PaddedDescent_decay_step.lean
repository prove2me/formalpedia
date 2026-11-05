-- Prove2me | solution 1 for PaddedDescent.decay_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:08:54.063475+00:00
-- url     : https://prove2.me/submissions/5a2bc05e-4195-4ef9-8424-4803d3a1bfde

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

set_option autoImplicit false
section
section
set_option exponentiation.threshold 1024
open PaddedDescent
open WidthK (theta bsum leafC)
open WidthK.Thresholds
namespace PaddedDescent
theorem _root_.solution (s : ℕ) :
    8963 ^ 19 * (8 * (s + 3 + 2 ^ 15) ^ 6) ≤ 10000 ^ 19 * (s + 2 ^ 15) ^ 6 := by
  have hx : (s + 3 + 2 ^ 15) * 2 ^ 15 ≤ (2 ^ 15 + 3) * (s + 2 ^ 15) := by omega
  have hnum : 8963 ^ 19 * (8 * (2 ^ 15 + 3) ^ 6) ≤ 10000 ^ 19 * (2 ^ 15) ^ 6 := by norm_num
  obtain ⟨A, hA⟩ : ∃ A, A = 8963 ^ 19 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = 10000 ^ 19 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ 15 := ⟨_, rfl⟩
  rw [← hA, ← hB, ← hM] at hnum ⊢
  rw [← hM] at hx
  refine Nat.le_of_mul_le_mul_right ?_ (show 0 < M ^ 6 by rw [hM]; norm_num)
  calc A * (8 * (s + 3 + M) ^ 6) * M ^ 6 = A * 8 * ((s + 3 + M) * M) ^ 6 := by ring
    _ ≤ A * 8 * ((M + 3) * (s + M)) ^ 6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx 6)
    _ = A * (8 * (M + 3) ^ 6) * (s + M) ^ 6 := by ring
    _ ≤ B * M ^ 6 * (s + M) ^ 6 := Nat.mul_le_mul_right _ hnum
    _ = B * (s + M) ^ 6 * M ^ 6 := by ring
end PaddedDescent
