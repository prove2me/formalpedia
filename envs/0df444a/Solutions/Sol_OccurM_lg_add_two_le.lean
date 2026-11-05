-- Prove2me | solution 1 for OccurM.lg_add_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:57.865972+00:00
-- url     : https://prove2.me/submissions/586a10b1-b69b-45f2-8773-982129b27243

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
import Theorems.Thm_VariableBound_Paper_lg_mono


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (hm : 2 ≤ m) : lg ((m : ℝ) + 2) ≤ 2 * lg m := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h : lg ((m : ℝ) ^ 2) = 2 * lg m := by
    unfold lg
    rw [Real.logb_pow]
    norm_num
  rw [← h]
  exact lg_mono (by linarith) (by nlinarith)
end OccurM
