-- Prove2me | solution 1 for VariableBound.Spec.two_le_nbD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:34:18.367729+00:00
-- url     : https://prove2.me/submissions/2af18b6d-a3ee-45f6-ae34-2fe0945fe5a6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Spec
import Theorems.Thm_VariableBound_Spec_nb_count

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Spec
namespace VariableBound.Spec
theorem _root_.solution (n Δ : ℕ) (hΔ : 1 ≤ Δ) (h : (2 * Δ) ^ 2 ≤ 2 ^ n) : 2 ≤ nbD n Δ := by
  obtain ⟨h1, -⟩ := nb_count n Δ hΔ
  unfold nbD
  generalize ((List.range (Nat.log 2 n + 1)).filter fun a => decide ((2 * Δ) ^ 2 ^ a ≤ 2 ^ n)).length = c at h1
  have hc : 2 ≤ c := by
    by_contra hlt
    have h3 : (2 * Δ) ^ 2 ^ c ≤ (2 * Δ) ^ 2 :=
      Nat.pow_le_pow_right (by omega) (by calc 2 ^ c ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
                                            _ = 2 := by norm_num)
    omega
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (c - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
end VariableBound.Spec
