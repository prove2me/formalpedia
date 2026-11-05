-- Prove2me | solution 1 for Wrap.Arith.sq_mul_lg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:56:23.227382+00:00
-- url     : https://prove2.me/submissions/fbb85c62-6d8c-46a7-b72b-152ed02e13c8

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
import Theorems.Thm_Wrap_Arith_lg_le_two_mul_sub
import Theorems.Thm_Wrap_Arith_one_le_lg_real

set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : x ^ 2 * lg y ≤ y ^ 2 * lg x := by
  have hx0 : 0 < x := by linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = y / x := ⟨_, rfl⟩
  have ht1 : 1 ≤ t := by rw [ht]; exact (one_le_div hx0).2 hxy
  have hy : y = x * t := by rw [ht]; field_simp
  have hl1 := one_le_lg_real hx
  have hlt := lg_le_two_mul_sub ht1
  have hly : lg y = lg x + lg t := by
    rw [hy]
    unfold lg
    exact Real.logb_mul hx0.ne' (by linarith)
  have key : lg x + lg t ≤ t ^ 2 * lg x := by
    nlinarith [mul_nonneg (sq_nonneg (t - 1)) (by linarith : (0 : ℝ) ≤ lg x), mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hl1)]
  rw [hly, hy]
  calc x ^ 2 * (lg x + lg t) ≤ x ^ 2 * (t ^ 2 * lg x) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = (x * t) ^ 2 * lg x := by ring
end Wrap.Arith
