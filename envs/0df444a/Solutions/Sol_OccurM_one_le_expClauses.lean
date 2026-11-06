-- Prove2me | solution 1 for OccurM.one_le_expClauses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:47.407979+00:00
-- url     : https://prove2.me/submissions/9a83a758-e5b3-4768-89e5-eb67414b723d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_Time
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OccurM_Arith
import Theorems.Thm_OccurM_one_le_lg_rpow
import Theorems.Thm_OccurM_lg_rpow_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Paper_lg_le_sub_one


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (h0 : 0 ≤ α) (h1 : α ≤ 1) (hk : 1 ≤ k) (hm : 2 ≤ m) : 1 ≤ expClauses α k m := by
  have hp := one_le_lg_rpow h0 hm
  have hle : lg m ^ α ≤ m := (lg_rpow_le h1 hm).trans (by linarith [lg_le_sub_one (by omega : 1 ≤ m)])
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold expClauses
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hk') hm0]
end OccurM
