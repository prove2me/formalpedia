-- Prove2me | solution 1 for StepSparsify.stAlphaS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:45:10.115522+00:00
-- url     : https://prove2.me/submissions/c30a13ce-faa7-447e-a691-946af07aff31

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

set_option autoImplicit false
section
section
open StepSparsify
open Finset PaddedDescent UniformInK SparsificationLemma
namespace StepSparsify
theorem _root_.solution : StAlphaS := by
  intro k s
  obtain ⟨K, hK⟩ : ∃ K, max k 3 = K + 1 := ⟨max k 3 - 1, by omega⟩
  rw [alphaS, hK, Cal.alphaC, Cal.logC, Cal.xC, Nat.add_sub_cancel]
  have e1 : (32 : ℚ) * (((K + 1 : ℕ) : ℚ) - 1) ^ 2 / (1 / 2 ^ s) = ((32 * K ^ 2 * 2 ^ s : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  rw [e1, Nat.ceil_natCast]
  have e2 : (2 : ℚ) * (((K + 1 : ℕ) : ℚ) - 1) ^ 2 / (1 / 2 ^ s) * ((Nat.clog 2 (32 * K ^ 2 * 2 ^ s) : ℕ) : ℚ)
      = ((2 * K ^ 2 * 2 ^ s * Nat.clog 2 (32 * K ^ 2 * 2 ^ s) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  rw [e2, Nat.ceil_natCast]
end StepSparsify
