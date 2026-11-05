-- Prove2me | solution 1 for VariableBound.Paper.timeMin_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:53:26.883387+00:00
-- url     : https://prove2.me/submissions/e65bc830-2b0a-4316-9cfb-6254ea8aede2

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
import Theorems.Thm_VariableBound_Paper_two_le_base
import Theorems.Thm_VariableBound_Paper_expN_eq
import Theorems.Thm_VariableBound_Paper_expM_eq

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution (C : ℕ) {m n : ℕ} (hm : 2 ≤ m) (hn : 4 ≤ n) : timeMin C 3 m n ≤ timeMin3 (9 * C) m n := by
  unfold timeMin timeMin3
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  have hA : 0 ≤ (m : ℝ) / Real.sqrt (lg m) := by positivity
  have hB : 0 ≤ (n : ℝ) * lg (lg n) / Real.sqrt (lg n) := by linarith [two_le_base hn]
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have h : min (expM 3 m) (expN 3 n) ≤ 9 * min ((m : ℝ) / Real.sqrt (lg m)) ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 9), expM_eq, expN_eq]
    refine min_le_min ?_ ?_
    · push_cast; linarith
    · push_cast; linarith
  calc (C : ℝ) * min (expM 3 m) (expN 3 n) ≤ (C : ℝ) * (9 * min ((m : ℝ) / Real.sqrt (lg m)) ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) :=
        mul_le_mul_of_nonneg_left h hC0
    _ = ((9 * C : ℕ) : ℝ) * min ((m : ℝ) / Real.sqrt (lg m)) ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) := by push_cast; ring
end VariableBound.Paper
