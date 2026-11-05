-- Prove2me | solution 1 for ThmVariables.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:17:46.534655+00:00
-- url     : https://prove2.me/submissions/fa01af2f-93bf-4410-83b4-b3bfd267f177

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmVariables_Defs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_ThmVariables_Bound
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open ThmVariables
open Turing CliqueLevels MainTheoremForms VariableBound.Paper
open Sat3 (CNF)
variable {K : ℕ → ℕ} {e : ℕ → ℝ} {C₀ : ℕ}
namespace ThmVariables
theorem _root_.solution (hL : Levels K e C₀) {n : ℕ} (hn : K 0 ^ 17 ≤ n) : ∃ l, ThmVariables.IsLevel K n l := by
  have hmono : StrictMono K := strictMono_nat_of_lt_succ hL.K_lt
  refine ⟨Nat.findGreatest (fun l => K l ^ 17 ≤ n) n, Nat.findGreatest_spec (P := fun l => K l ^ 17 ≤ n) (Nat.zero_le n) hn, ?_⟩
  by_contra h
  have h' := not_lt.1 h
  have h1 := hmono.le_apply (x := Nat.findGreatest (fun l => K l ^ 17 ≤ n) n + 1)
  have h2 : K (Nat.findGreatest (fun l => K l ^ 17 ≤ n) n + 1) ≤ K (Nat.findGreatest (fun l => K l ^ 17 ≤ n) n + 1) ^ 17 := Nat.le_self_pow (by norm_num) _
  exact Nat.findGreatest_is_greatest (P := fun l => K l ^ 17 ≤ n) (Nat.lt_succ_self _) ((h1.trans h2).trans h') h'
end ThmVariables
