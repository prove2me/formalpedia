-- Prove2me | solution 1 for VariableBound.ArithNat.gPD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:36:39.201209+00:00
-- url     : https://prove2.me/submissions/e478fe77-8ce6-416e-9e49-a3ddb6886813

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
import Theorems.Thm_ClauseBound_ParityChecks_clog_le_size
import Theorems.Thm_ClauseBound_ParityChecks_size_mul_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_UniformInK_ArithNat_two_le_D
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.ArithNat VariableBound.Net
variable {β k K n C₀ : ℕ}
namespace VariableBound.ArithNat
theorem _root_.solution (hB : StBounds) (hβ : 1 ≤ β) (hn : 1 ≤ n) (hg : 3 * K ^ 8 ≤ n) :
    3 * K ^ 8 * PbD K n (2 ^ β) ≤ n * 2 ^ β * (842 * (β + 3) + 4 * n.size) := by
  have h := (hB 0 K n (2 ^ β) hn (two_le_D hβ)).2
  unfold tbMax sbMax at h
  rw [LD_two_pow] at h
  refine h.trans ?_
  have hc : Nat.clog 2 (2 ^ β * n) ≤ β + n.size := (clog_le_size _).trans (size_mul_le β n)
  have hD : 1 ≤ 2 ^ β := Nat.one_le_two_pow
  generalize Nat.clog 2 (2 ^ β * n) = c at hc
  generalize 3 * K ^ 8 = g at hg
  generalize n.size = z at hc
  generalize 2 ^ β = D at hD
  have h1 : 1 + D * (c + 33 * (β + 1) + 1 + 3) ≤ D * (34 * β + z + 38) := by
    calc 1 + D * (c + 33 * (β + 1) + 1 + 3) ≤ D + D * (34 * β + z + 37) := Nat.add_le_add hD (Nat.mul_le_mul_left _ (by omega))
      _ = D * (34 * β + z + 38) := by ring
  calc 2 * (n + g) * (1 + D * (c + 33 * (β + 1) + 1 + 3)) + 2 * (10 * n + g) * (32 * D * (β + 1)) + g
      ≤ 4 * n * (D * (34 * β + z + 38)) + 22 * n * (32 * D * (β + 1)) + n * D :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul (by omega) h1) (Nat.mul_le_mul_right _ (by omega))) (hg.trans (Nat.le_mul_of_pos_right _ hD))
    _ = n * D * (840 * β + 4 * z + 857) := by ring
    _ ≤ n * D * (842 * (β + 3) + 4 * z) := Nat.mul_le_mul_left _ (by omega)
end VariableBound.ArithNat
