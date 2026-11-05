-- Prove2me | solution 1 for UniformInK.stParU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:35:50.10107+00:00
-- url     : https://prove2.me/submissions/c98005f8-d7f2-4cd2-91b2-ce924f06da84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_UniformInK_Top_Leaves
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_ClauseBound_ParityChecks_BudgetOL
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_UniformInK_Top_Budget
import Theorems.Thm_UniformInK_Budget_leafCU_add_two_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_PaddedDescent_two_pow_le_tauOf
import Theorems.Thm_UniformInK_Leaves_bsumU_tauOf
import Theorems.Thm_UniformInK_Leaves_sq_le_of_s0U_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open UniformInK
open PaddedDescent ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves UniformInK.Budget
namespace UniformInK
theorem _root_.solution : StParU := by
  intro k s hk
  have h17 := two_pow_le_tauOf s
  refine ⟨?_, fun hs => ?_⟩
  · rw [← bsumU_tauOf]
    exact leafCU_add_two_le (le_trans (by norm_num) h17) hk
  · have h1 : k ^ 2 ≤ 2 ^ s := sq_le_of_s0U_le hs
    have h2 : 8 * 2 ^ s ≤ tauOf s := by
      rw [tauOf, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : k ≤ k ^ 2 := by nlinarith
    omega
end UniformInK
