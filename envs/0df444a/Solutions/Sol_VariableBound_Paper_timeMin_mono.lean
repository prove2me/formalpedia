-- Prove2me | solution 1 for VariableBound.Paper.timeMin_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:54:51.835185+00:00
-- url     : https://prove2.me/submissions/4d429146-8931-4a63-8e25-e4a55cb0d0c7

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution {C C' : ℕ} (h : C ≤ C') {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) : timeMin C k m n ≤ timeMin C' k m n := by
  unfold timeMin
  have hX : 0 ≤ min (expM k m) (expN k n) := le_min (by linarith [two_le_expM hk hm]) (by linarith [two_le_expN hk hn])
  exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hX))
end VariableBound.Paper
