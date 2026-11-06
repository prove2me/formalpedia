-- Prove2me | solution 1 for VariableBound.Count.sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:59.572334+00:00
-- url     : https://prove2.me/submissions/3e694b29-867d-45d9-996b-230e80dc82ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_VariableBound_Count_Correct

set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.ParityChecks AppVariables VariableBound.Net Finset
namespace VariableBound.Count
theorem _root_.solution (n Δ : ℕ) (h : 2 * LD Δ ≤ n) : (2 * Δ) ^ 2 ≤ 2 ^ n := by
  have h1 : 2 * Δ ≤ 2 ^ LD Δ := Nat.le_pow_clog (by norm_num) _
  calc (2 * Δ) ^ 2 ≤ (2 ^ LD Δ) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 2 ^ (LD Δ * 2) := (pow_mul 2 _ 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
end VariableBound.Count
