-- Prove2me | solution 1 for VariableBound.Arith.const_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:07.767693+00:00
-- url     : https://prove2.me/submissions/778a441d-a368-47e5-82ea-f6235ea76322

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_UniformInK_Top_ArithTop
import Definitions.Def_UniformInK_Top_ArithTop
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Top_ArithTop
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open VariableBound VariableBound.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks UniformInK UniformInK.Arith
namespace VariableBound.Arith
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (C₀ A₁ : ℕ) : 140 * k * (35 * k) + ccD k C₀ * A₁ + 1 ≤ (140 * 35 + (ccD 0 C₀ + 140) * A₁ + 1) * k ^ 2 := by
  have h1 : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
  have h2 : 1 ≤ k ^ 2 := hk.trans h1
  have e1 : ccD k C₀ = ccD 0 C₀ + 140 * k := by unfold ccD; ring
  have h3 : ccD k C₀ ≤ (ccD 0 C₀ + 140) * k ^ 2 := by
    rw [e1]
    calc ccD 0 C₀ + 140 * k ≤ ccD 0 C₀ * k ^ 2 + 140 * k ^ 2 := Nat.add_le_add (Nat.le_mul_of_pos_right _ h2) (Nat.mul_le_mul_left _ h1)
      _ = (ccD 0 C₀ + 140) * k ^ 2 := by ring
  calc 140 * k * (35 * k) + ccD k C₀ * A₁ + 1 ≤ 140 * 35 * k ^ 2 + (ccD 0 C₀ + 140) * k ^ 2 * A₁ + k ^ 2 :=
        Nat.add_le_add (Nat.add_le_add (by rw [show 140 * k * (35 * k) = 140 * 35 * k ^ 2 by ring]) (Nat.mul_le_mul_right _ h3)) h2
    _ = (140 * 35 + (ccD 0 C₀ + 140) * A₁ + 1) * k ^ 2 := by ring
end VariableBound.Arith
