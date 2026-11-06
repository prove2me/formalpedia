-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.size_query_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:59:22.887299+00:00
-- url     : https://prove2.me/submissions/5b44d542-e9f5-447e-8260-4a196c8c9969

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_CountedToPadded_Tables
import Definitions.Def_CountedToPadded_Need
import Definitions.Def_CountedToPadded_Pick
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_StepMachines_Prog_SideBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_CountedToPadded_Levels
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_size_bools
import Theorems.Thm_Groundwork_RebalanceArith_size_le
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_prod
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_prod



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Eight.SecNetworks Printed CliqueLevels
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {K lam : ℕ} {x : TableQuery} (h1 : x.1 < K) (h2 : x.2.length = (K - 1) * lam) : size x ≤ K + 2 * (K * lam) + 2 := by
  have h3 : Nat.size x.1 ≤ x.1 := Nat.size_le.2 Nat.lt_two_pow_self
  have h4 : (K - 1) * lam ≤ K * lam := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  rw [size_prod, size_nat, size_bools, h2]
  omega
end QueryMachines.Bridge.Proof
