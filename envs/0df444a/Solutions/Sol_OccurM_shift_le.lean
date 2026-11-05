-- Prove2me | solution 1 for OccurM.shift_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:07:56.806105+00:00
-- url     : https://prove2.me/submissions/fb17c5a0-549e-424f-9250-a534e32924ed

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
import Theorems.Thm_VariableBound_Paper_one_le_lg


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (h0 : 0 ≤ α) (k : ℕ) (hm : 2 ≤ m) : (k : ℝ) * m * SatM.rPow α m ≤ expClauses α k m := by
  have h1 := one_le_lg hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp : 0 < lg m ^ α := Real.rpow_pos_of_pos (by linarith) α
  have hle : lg m ^ α ≤ lg ((m : ℝ) + 2) ^ α := Real.rpow_le_rpow (by linarith) (lg_mono hm0 (by linarith)) h0
  unfold SatM.rPow expClauses
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by positivity) hp hle
end OccurM
