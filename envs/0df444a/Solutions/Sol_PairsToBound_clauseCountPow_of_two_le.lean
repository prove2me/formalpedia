-- Prove2me | solution 1 for PairsToBound.clauseCountPow_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:08:10.638449+00:00
-- url     : https://prove2.me/submissions/aea8afdc-1995-445a-bf80-36836b9a6229

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Exhaust
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PairsToBound_clauseCountPowStmt


set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution (k : ℕ) {n : ℕ} (hn : 2 ≤ n) : (2 * n + 1) ^ k ≤ n ^ (3 * k) := by
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) k
  · exact (clauseCountPowStmt k n h).trans (Nat.pow_le_pow_right (by omega) (by omega))
end PairsToBound
