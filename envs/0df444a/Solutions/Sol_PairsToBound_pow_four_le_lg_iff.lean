-- Prove2me | solution 1 for PairsToBound.pow_four_le_lg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:48:58.806078+00:00
-- url     : https://prove2.me/submissions/3554e26f-5780-4a6f-9e47-0b39fd974634

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Rename_Defs
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_VariableBound_Paper_Rename_Cert
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Unary
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_FrontEnd

set_option autoImplicit false
section
section
open PairsToBound
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg MainTheoremForms VariableBound.Rename
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : (k : ℝ) ^ 4 ≤ lg n ↔ 2 ^ (k ^ 4) ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : (0 : ℝ) < (k : ℝ) ^ 4 := by
      have : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
    have h1 : 0 < 2 ^ (k ^ 4) := Nat.pos_of_ne_zero (by positivity)
    constructor
    · intro h
      rw [lg, Nat.cast_zero, Real.logb_zero] at h
      linarith
    · intro h
      omega
  · have e : (2 : ℝ) ^ ((k : ℝ) ^ 4) = ((2 ^ (k ^ 4) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, Real.rpow_natCast]
      push_cast
      rfl
    rw [lg, Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hn), e, Nat.cast_le]
end PairsToBound
