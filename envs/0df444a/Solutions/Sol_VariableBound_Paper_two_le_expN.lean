-- Prove2me | solution 1 for VariableBound.Paper.two_le_expN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:52:36.261842+00:00
-- url     : https://prove2.me/submissions/6d2e81fd-ff2d-4833-8843-10c3d4905963

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms
namespace VariableBound.Paper
theorem _root_.solution {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : 2 ≤ expN k n := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h := two_le_base hn
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  rw [expN_eq]
  nlinarith
end VariableBound.Paper
