-- Prove2me | solution 1 for VariableBound.stBudgetD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:46:19.618849+00:00
-- url     : https://prove2.me/submissions/753e8832-fda9-4ff7-9674-0ff1c57604a4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_UniformInK_Top_Budget
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_VariableBound_Top_Budget
import Theorems.Thm_VariableBound_Budget_nProf_le
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_le_four
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_nProf_le
import Theorems.Thm_ClauseBound_ParityChecks_BudgetOL_stack_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_UniformInK_Budget_stack_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open VariableBound
open PaddedDescent ClauseBound.ParityChecks.BudgetOL UniformInK VariableBound.Net
namespace VariableBound
theorem _root_.solution (hL : StLeavesU) : StBudgetD := by
  intro k K n s F hk hs hF
  have up : ∀ {x t : ℕ}, x ≤ 2 ^ t → t ≤ restD k K n s → x ≤ F := fun h1 h2 => h1.trans ((Nat.pow_le_pow_right (by norm_num) h2).trans hF)
  refine ⟨up (Budget.nProf_le _ _) (le_four _ _ _ _).1, up (Nat.lt_size_self _).le (le_four _ _ _ _).2.1, ?_, up (UniformInK.Budget.stack_le hk n s) (le_four _ _ _ _).2.2.2⟩
  have h1 := hL k n s hk hs
  have h2 : 2 ^ (n / 2 ^ s + 1 + 1) ≤ F := up le_rfl (le_four _ _ _ _).2.2.1
  rw [pow_succ] at h2
  omega
end VariableBound
