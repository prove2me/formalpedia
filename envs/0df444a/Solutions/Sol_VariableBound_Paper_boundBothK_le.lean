-- Prove2me | solution 1 for VariableBound.Paper.boundBothK_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:05:53.724705+00:00
-- url     : https://prove2.me/submissions/6386d10a-3f6b-4d8f-98f1-2120503de707

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
import Theorems.Thm_VariableBound_Paper_two_le_expM
import Theorems.Thm_VariableBound_Paper_two_le_expN
import Theorems.Thm_VariableBound_Paper_shiftM_le
import Theorems.Thm_VariableBound_Paper_shiftN_le
import Theorems.Thm_VariableBound_Paper_absorb

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution (C : ℕ) {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) :
    SatM.boundBothK (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) C k n m ≤ timeMin (3 * C) k m n := by
  unfold SatM.boundBothK timeMin
  refine Nat.floor_le_floor (absorb C ?_ ?_)
  · have hM := shiftM_le k hm
    have hN := shiftN_le k hn
    have hM2 := two_le_expM hk hm
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_min ((min_le_right _ _).trans (by linarith)) ((min_le_left _ _).trans hN)
  · exact le_min (by linarith [two_le_expM hk hm]) (by linarith [two_le_expN hk hn])
end VariableBound.Paper
