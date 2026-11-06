-- Prove2me | solution 1 for VariableBound.ArithNat.size_objMax_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:40:56.63312+00:00
-- url     : https://prove2.me/submissions/c2ee098b-87de-444f-a88a-e01936e62af2

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
import Theorems.Thm_ClauseBound_TopN_mul_le_pow
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_RebalanceArith_size_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.ArithNat VariableBound.Net
variable {β k K n C₀ : ℕ}
namespace VariableBound.ArithNat
theorem _root_.solution (β n : ℕ) : Nat.size (objMax n (2 ^ β)) ≤ 2 * β + n.size + 10 := by
  rw [Nat.size_le]
  unfold objMax sbMax
  rw [LD_two_pow]
  have h1 : β + 1 ≤ 2 ^ β := Nat.lt_two_pow_self
  have h2 : n ≤ 2 ^ n.size := (Nat.lt_size_self n).le
  have h3 : 320 * (β + 1) + 1 ≤ 2 ^ (9 + β) := by rw [pow_add]; omega
  calc 10 * n * (32 * 2 ^ β * (β + 1)) + 2 ^ β * n = n * 2 ^ β * (320 * (β + 1) + 1) := by ring
    _ ≤ 2 ^ (n.size + β + (9 + β)) := mul_le_pow (mul_le_pow h2 le_rfl) h3
    _ < 2 ^ (2 * β + n.size + 10) := Nat.pow_lt_pow_right (by norm_num) (by omega)
end VariableBound.ArithNat
