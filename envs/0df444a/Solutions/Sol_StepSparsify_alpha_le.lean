-- Prove2me | solution 1 for StepSparsify.alpha_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:45:19.816225+00:00
-- url     : https://prove2.me/submissions/107578c4-68ae-40e0-a96c-5e8b3aa94213

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepSparsify_Defs
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_UniformInK_Top_Leaves
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_StepSparsify_CalNumbers
import Theorems.Thm_StepSparsify_eps_pos
import Theorems.Thm_StepSparsify_eps_le_one
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_SparsificationLemma_Cal_stAlphaLe


set_option autoImplicit false
section
section
open StepSparsify
open Finset PaddedDescent UniformInK SparsificationLemma
namespace StepSparsify
theorem _root_.solution {k s : ℕ} (hk : 1 ≤ k) (hs : k ^ 2 ≤ 2 ^ s) : 32 * alphaS k s ≤ tauOf s ^ 2 := by
  have h1 : 32 * (alphaS k s : ℝ) ≤ (8 * ((max k 3 : ℕ) : ℝ) / (((1 / 2 ^ s : ℚ)) : ℝ)) ^ 3 :=
    Cal.stAlphaLe (max k 3) (1 / 2 ^ s) (le_max_right k 3) (eps_pos s) (eps_le_one s)
  have e : (8 * ((max k 3 : ℕ) : ℝ) / (((1 / 2 ^ s : ℚ)) : ℝ)) ^ 3 = (((8 * max k 3 * 2 ^ s) ^ 3 : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [e] at h1
  have h2 : 32 * alphaS k s ≤ (8 * max k 3 * 2 ^ s) ^ 3 := by exact_mod_cast h1
  have h3 : max k 3 ≤ 3 * k := by omega
  have h4 : k ≤ 2 ^ s := le_trans (by nlinarith) hs
  have h5 : 8 * max k 3 * 2 ^ s ≤ 2 ^ (2 * s + 5) := by
    calc 8 * max k 3 * 2 ^ s ≤ 8 * (3 * 2 ^ s) * 2 ^ s :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (h3.trans (Nat.mul_le_mul_left _ h4)))
      _ ≤ 32 * (2 ^ s * 2 ^ s) := by nlinarith [Nat.zero_le (2 ^ s * 2 ^ s)]
      _ = 2 ^ (2 * s + 5) := by ring
  calc 32 * alphaS k s ≤ (8 * max k 3 * 2 ^ s) ^ 3 := h2
    _ ≤ (2 ^ (2 * s + 5)) ^ 3 := Nat.pow_le_pow_left h5 3
    _ = 2 ^ ((2 * s + 5) * 3) := by rw [← pow_mul]
    _ ≤ 2 ^ ((4 * s + 17) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = tauOf s ^ 2 := by rw [tauOf, ← pow_mul]
end StepSparsify
