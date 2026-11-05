-- Prove2me | solution 1 for VariableBound.Paper.boundNK_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:53:44.016186+00:00
-- url     : https://prove2.me/submissions/e6f0737f-e680-408c-810f-c521b95ed274

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
import Theorems.Thm_VariableBound_Paper_two_le_expN
import Theorems.Thm_VariableBound_Paper_shiftN_le
import Theorems.Thm_VariableBound_Paper_absorb

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution (C : ℕ) {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : SatM.boundNK (SatK.rN 1 (1 / 2)) C k n ≤ timeN (3 * C) k n := by
  unfold SatM.boundNK timeN
  refine Nat.floor_le_floor ?_
  have e : (C : ℝ) * (k : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n = (C : ℝ) * ((k : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n) := by ring
  rw [e]
  exact absorb C (shiftN_le k hn) (by linarith [two_le_expN hk hn])
end VariableBound.Paper
