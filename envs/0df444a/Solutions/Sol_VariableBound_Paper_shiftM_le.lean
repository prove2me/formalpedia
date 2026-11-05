-- Prove2me | solution 1 for VariableBound.Paper.shiftM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:42:06.282003+00:00
-- url     : https://prove2.me/submissions/5890f81a-b63e-4ba4-90c2-30a9a0468659

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_VariableBound_Paper_Arith
import Theorems.Thm_VariableBound_Paper_lg_mono
import Theorems.Thm_VariableBound_Paper_one_le_lg

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution (k : ℕ) {m : ℕ} (hm : 2 ≤ m) : (k : ℝ) * m * SatM.rPow (1 / 2) m ≤ expM k m := by
  have h1 := one_le_lg hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hs : 0 < Real.sqrt (lg m) := Real.sqrt_pos.2 (by linarith)
  have hle : Real.sqrt (lg m) ≤ Real.sqrt (lg ((m : ℝ) + 2)) := Real.sqrt_le_sqrt (lg_mono hm0 (by linarith))
  unfold SatM.rPow expM
  rw [← Real.sqrt_eq_rpow, mul_one_div]
  exact div_le_div_of_nonneg_left (by positivity) hs hle
end VariableBound.Paper
