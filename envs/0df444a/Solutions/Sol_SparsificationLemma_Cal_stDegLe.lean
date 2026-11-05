-- Prove2me | solution 1 for SparsificationLemma.Cal.stDegLe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:43:18.013671+00:00
-- url     : https://prove2.me/submissions/09e6da31-00fe-47a8-8ca0-f3ef0ad7c4f0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Definitions.Def_SparsificationLemma_Cal_Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Theorems.Thm_SparsificationLemma_Cal_stAlpha
import Theorems.Thm_SparsificationLemma_Cal_stAlphaLe

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
namespace SparsificationLemma.Cal
theorem _root_.solution : StDegLe := by
  intro k ε hk h0 h1
  obtain ⟨-, hα, -, -, -⟩ := stAlpha k ε hk h0 h1
  have hle := stAlphaLe k ε hk h0 h1
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have h1R : (ε : ℝ) ≤ 1 := by exact_mod_cast h1
  have hB : 1 ≤ 8 * (k : ℝ) / (ε : ℝ) := by rw [le_div_iff₀ h0R]; linarith
  have hN : 2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) ≤ (32 * alphaC k ε) ^ (k - 1) := by
    have hp : 1 ≤ (32 * alphaC k ε) ^ (k - 2) := Nat.one_le_pow _ _ (by omega)
    have he : (32 * alphaC k ε) ^ (k - 1) = 32 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) := by
      rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]; ring
    rw [he]
    nlinarith
  calc ((2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) : ℕ) : ℝ)
      ≤ (((32 * alphaC k ε) ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hN
    _ = (32 * (alphaC k ε : ℝ)) ^ (k - 1) := by push_cast; ring
    _ ≤ ((8 * (k : ℝ) / (ε : ℝ)) ^ 3) ^ (k - 1) := pow_le_pow_left₀ (by positivity) hle _
    _ = (8 * (k : ℝ) / (ε : ℝ)) ^ (3 * (k - 1)) := by rw [← pow_mul]
    _ ≤ (8 * (k : ℝ) / (ε : ℝ)) ^ (3 * k) := pow_le_pow_right₀ hB (by omega)
end SparsificationLemma.Cal
