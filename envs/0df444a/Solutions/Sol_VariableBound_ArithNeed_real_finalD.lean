-- Prove2me | solution 1 for VariableBound.ArithNeed.real_finalD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:41:56.75172+00:00
-- url     : https://prove2.me/submissions/8cbb4ab1-5960-43e3-9f57-0bef18efc5f7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithNeed
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open VariableBound VariableBound.ArithNeed
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL UniformInK VariableBound.Net
namespace VariableBound.ArithNeed
theorem _root_.solution {e n k b ck q cA Z R3 N : ℝ} (he0 : 0 ≤ e) (hn0 : 0 ≤ n) (hk0 : 0 ≤ k) (hq : 1 ≤ q) (hcA : 0 ≤ cA)
    (rb : b ≤ ck * q) (hZ : Z ≤ e * (140 * k * n * b) + cA * (n * e)) (hR3 : R3 ≤ n * e) (hN : N ≤ Z + R3) :
    N ≤ (140 * k * ck + cA + 1) * n * e * q := by
  have hne : 0 ≤ n * e := mul_nonneg hn0 he0
  have hne2 : n * e ≤ n * e * q := le_mul_of_one_le_right hne hq
  have hmain : e * (140 * k * n * b) ≤ (140 * k * ck) * (n * e * q) := by
    calc e * (140 * k * n * b) = 140 * k * (n * e) * b := by ring
      _ ≤ 140 * k * (n * e) * (ck * q) := mul_le_mul_of_nonneg_left rb (mul_nonneg (mul_nonneg (by norm_num) hk0) hne)
      _ = (140 * k * ck) * (n * e * q) := by ring
  have h2 := mul_le_mul_of_nonneg_left hne2 hcA
  have e1 : (140 * k * ck + cA + 1) * n * e * q = (140 * k * ck) * (n * e * q) + cA * (n * e * q) + n * e * q := by ring
  rw [e1]
  linarith
end VariableBound.ArithNeed
