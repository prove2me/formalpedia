-- Prove2me | solution 1 for VariableBound.Spec.tb_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:31:29.814305+00:00
-- url     : https://prove2.me/submissions/16ffcbc2-09d8-4d91-bf85-3eb28eacdec7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Params_Spec

set_option autoImplicit false
section
section
open VariableBound
open AppVariables
open VariableBound.Spec
namespace VariableBound.Spec
theorem _root_.solution (m nb rb c : ℕ) (hnb : 1 ≤ nb) : (m : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ c ↔ m * (15 * nb + 16) ^ rb ≤ 2 ^ c * (15 * nb) ^ rb := by
  have h0 : (0 : ℚ) < 15 * nb := by
    have : (1 : ℚ) ≤ nb := by exact_mod_cast hnb
    linarith
  have e : 1 + pp nb = (15 * nb + 16) / (15 * nb) := by
    unfold pp
    field_simp
  rw [e, div_pow, mul_div_assoc', div_le_iff₀ (pow_pos h0 rb)]
  exact_mod_cast Iff.rfl
end VariableBound.Spec
