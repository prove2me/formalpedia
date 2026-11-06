-- Prove2me | solution 1 for UniformInK.ArithNat.WofU_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:39:28.35019+00:00
-- url     : https://prove2.me/submissions/c796e7ba-f817-4717-a685-4a2d3e28d0b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_UniformInK_Top_ArithNat
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK UniformInK.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks
variable {β k K n C₀ : ℕ}
namespace UniformInK.ArithNat
theorem _root_.solution (hK : 1 ≤ K) : (β + 3) * 2 ^ β ≤ WofU β K ∧ (β + 3) ^ 2 * K.size ≤ WofU β K ∧
    (β + 3) ^ 2 ≤ WofU β K ∧ (β + 3) * K.size ≤ WofU β K ∧ K.size ≤ WofU β K ∧ β + 3 ≤ WofU β K ∧ 2 ^ β ≤ WofU β K ∧ 1 ≤ WofU β K := by
  unfold WofU
  have hY : 1 ≤ K.size := Nat.size_pos.2 hK
  have hD : 1 ≤ 2 ^ β := Nat.one_le_two_pow
  generalize K.size = Y at hY
  generalize 2 ^ β = D at hD
  have hb : 1 ≤ β + 3 := by omega
  generalize β + 3 = b at hb
  have hbb : b ≤ b ^ 2 := Nat.le_self_pow (by norm_num) b
  have h1 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb
  have m1 : b * D ≤ b ^ 2 * D * Y := by
    calc b * D ≤ b ^ 2 * D := Nat.mul_le_mul_right _ hbb
      _ ≤ b ^ 2 * D * Y := Nat.le_mul_of_pos_right _ hY
  have m2 : b ^ 2 * Y ≤ b ^ 2 * D * Y := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hD)
  have m3 : b ^ 2 ≤ b ^ 2 * Y := Nat.le_mul_of_pos_right _ hY
  have m4 : b * Y ≤ b ^ 2 * Y := Nat.mul_le_mul_right _ hbb
  have m5 : Y ≤ b ^ 2 * Y := Nat.le_mul_of_pos_left _ h1
  have m6 : D ≤ b * D := Nat.le_mul_of_pos_left _ hb
  exact ⟨m1, m2, m3.trans m2, m4.trans m2, m5.trans m2, (hbb.trans m3).trans m2, m6.trans m1, (h1.trans m3).trans m2⟩
end UniformInK.ArithNat
