-- Prove2me | solution 1 for VariableBound.Budget.nProf_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:39:22.293393+00:00
-- url     : https://prove2.me/submissions/02a159fd-a43f-4fa2-90c0-186cf8a1c87c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_VariableBound_Top_Budget
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_succ_le_size
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open VariableBound VariableBound.Budget
open PaddedDescent.F ClauseBound.ParityChecks.BudgetOL
namespace VariableBound.Budget
theorem _root_.solution (g M : ℕ) : Mark.nProf g M 2 ≤ 2 ^ (g * g * 2 * Nat.size M) := by
  unfold Mark.nProf
  calc (M + 1) ^ (g * g * 2) ≤ (2 ^ Nat.size M) ^ (g * g * 2) := Nat.pow_le_pow_left (succ_le_size M) _
    _ = 2 ^ (g * g * 2 * Nat.size M) := by rw [← pow_mul, Nat.mul_comm (Nat.size M)]
end VariableBound.Budget
