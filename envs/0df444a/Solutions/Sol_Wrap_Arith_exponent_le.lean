-- Prove2me | solution 1 for Wrap.Arith.exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:19.664405+00:00
-- url     : https://prove2.me/submissions/2387c2a9-48e2-4b5a-a2e4-35f422c35277

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_Wrap_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_Wrap_ArithRate
import Theorems.Thm_Wrap_Arith_rate_eq
import Theorems.Thm_Wrap_Arith_div_sqrt_lg_mono
import Theorems.Thm_VariableBound_Paper_lg_add_four
import Theorems.Thm_VariableBound_Paper_lg_mono


set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution {n n' : ℕ} (hn' : 4 ≤ n') (hnn : n' ≤ n + 4) :
    (n' : ℝ) * lg (lg n') / Real.sqrt (lg n') ≤ ((n : ℝ) + 4) * SatK.rN 1 (1 / 2) n := by
  have h4 : (4 : ℝ) ≤ n' := by exact_mod_cast hn'
  have hle : (n' : ℝ) ≤ (n : ℝ) + 4 := by exact_mod_cast hnn
  obtain ⟨hL2, -, hl1, -, -⟩ := VariableBound.Paper.lg_add_four hn'
  have hmono := div_sqrt_lg_mono (by linarith) hle
  have hll : lg (lg n') ≤ lg (lg ((n : ℝ) + 4)) := VariableBound.Paper.lg_mono (by linarith) (VariableBound.Paper.lg_mono (by linarith) hle)
  rw [rate_eq]
  calc (n' : ℝ) * lg (lg n') / Real.sqrt (lg n') = (n' : ℝ) / Real.sqrt (lg n') * lg (lg n') := by ring
    _ ≤ ((n : ℝ) + 4) / Real.sqrt (lg ((n : ℝ) + 4)) * lg (lg ((n : ℝ) + 4)) :=
        mul_le_mul hmono hll (by linarith) (div_nonneg (by positivity) (Real.sqrt_nonneg _))
    _ = ((n : ℝ) + 4) * (lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4))) := by ring
end Wrap.Arith
