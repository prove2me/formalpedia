-- Prove2me | solution 1 for UniformInK.Arith.two_pow_s0U_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:06.641898+00:00
-- url     : https://prove2.me/submissions/d2c05539-a9ca-4643-932b-1e74dd2f6c2d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_UniformInK_Top_ArithTop
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open UniformInK UniformInK.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks
namespace UniformInK.Arith
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) : 2 ^ s0U k ≤ 4 * k ^ 2 := by
  have h1 : 2 ^ (k.size - 1) ≤ k := Nat.lt_size.1 (by have := Nat.size_pos.2 hk; omega)
  have h2 : k.size = (k.size - 1) + 1 := by have := Nat.size_pos.2 hk; omega
  have h3 : 2 ^ k.size ≤ 2 * k := by rw [h2, pow_succ]; omega
  calc 2 ^ s0U k = (2 ^ k.size) ^ 2 := by unfold s0U; rw [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * k) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = 4 * k ^ 2 := by ring
end UniformInK.Arith
