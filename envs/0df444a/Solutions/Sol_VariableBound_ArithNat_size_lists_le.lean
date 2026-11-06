-- Prove2me | solution 1 for VariableBound.ArithNat.size_lists_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:40:57.623708+00:00
-- url     : https://prove2.me/submissions/52e29b4a-3bb6-456f-b4af-7030bdd8402b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_UniformInK_Top_ArithNat
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNat
import Theorems.Thm_ClauseBound_ParityChecks_LD_two_pow
import Theorems.Thm_ClauseBound_ParityChecks_size_mul_le
import Theorems.Thm_ClauseBound_TopN_add_le_pow
import Theorems.Thm_ClauseBound_TopN_mul_le_pow
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.ArithNat VariableBound.Net
variable {β k K n C₀ : ℕ}
namespace VariableBound.ArithNat
theorem _root_.solution (β n : ℕ) : Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) ≤ 3 * β + 2 * n.size + 17 := by
  rw [Nat.size_le]
  unfold sbMax
  rw [LD_two_pow]
  have h1 : β + 1 ≤ 2 ^ β := Nat.lt_two_pow_self
  have h2 : n + 1 ≤ 2 ^ n.size := Nat.lt_size_self n
  have h3 : 10 * n + 1 ≤ 2 ^ (4 + n.size) := by rw [pow_add]; omega
  have h4 : 32 * 2 ^ β * (β + 1) + 1 ≤ 2 ^ (6 + β + β) := by
    have a1 : 32 * 2 ^ β * (β + 1) ≤ 2 ^ (5 + β + β) := mul_le_pow (mul_le_pow (by norm_num) le_rfl) h1
    exact add_le_pow (q := 0) a1 (by norm_num) (by omega) (by omega)
  have h5 : Nat.size (2 ^ β * n) + 2 ≤ 2 ^ (β + n.size + 2) := (Nat.add_le_add_right (size_mul_le β n) 2).trans Nat.lt_two_pow_self.le
  have h6 : 8 * (10 * n + 1) * (32 * 2 ^ β * (β + 1) + 1) * (Nat.size (2 ^ β * n) + 2) ≤ 2 ^ (3 + (4 + n.size) + (6 + β + β) + (β + n.size + 2)) :=
    mul_le_pow (mul_le_pow (mul_le_pow (by norm_num) h3) h4) h5
  calc 8 * (10 * n + 1) * (32 * 2 ^ β * (β + 1) + 1) * (Nat.size (2 ^ β * n) + 2) + 8 ≤ 2 ^ (3 * β + 2 * n.size + 16) :=
        add_le_pow (q := 3) h6 (by norm_num) (by omega) (by omega)
    _ < 2 ^ (3 * β + 2 * n.size + 17) := Nat.pow_lt_pow_right (by norm_num) (by omega)
end VariableBound.ArithNat
