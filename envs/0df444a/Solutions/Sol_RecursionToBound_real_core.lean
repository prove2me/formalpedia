-- Prove2me | solution 1 for RecursionToBound.real_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:49:59.64212+00:00
-- url     : https://prove2.me/submissions/47231fa1-b185-4f08-b4f0-146e9b60d8f3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_RecursionToBound_Defs
import Definitions.Def_VariableBound_Top_ArithDefs
import Definitions.Def_RecursionToBound_Numbers
import Definitions.Def_VariableBound_Top_ArithNat
import Definitions.Def_UniformInK_Top_ArithMaster
import Definitions.Def_VariableBound_Net_Main
import Definitions.Def_VariableBound_Net_StepCost
import Definitions.Def_VariableBound_Printed_VariablesA_Level
import Definitions.Def_VariableBound_Printed_VariablesA_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Definitions.Def_RecursionToBound_OneOutput

set_option autoImplicit false
section
section
open RecursionToBound
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.ParityChecks UniformInK VariableBound.Net MainTheoremForms VariableBound.Paper
namespace RecursionToBound
theorem _root_.solution {Kr e n W A C₀ M T1 T2 T3 R1 Rx gP U36 Ubr Lc Lg lam nd c1 c2 c3 c4 c5 c7 c8 c9 : ℝ}
    (hKr : 0 < Kr) (he0 : 0 < e) (he1 : e ≤ 1) (hn0 : 0 ≤ n) (hC0 : 0 ≤ C₀) (hgP0 : 0 ≤ gP) (hU36 : 0 ≤ U36)
    (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4) (h5 : 0 ≤ c5) (h7 : 0 ≤ c7) (h8 : 0 ≤ c8) (h9 : 0 ≤ c9) (hM : W ≤ A * Kr * e)
    (r1 : Kr * T1 ≤ c1 * (W * n)) (r2 : Kr * T2 ≤ c2 * (W * n)) (r3 : Kr * T3 ≤ c3 * (W * n)) (r4 : gP ≤ c4 * (W * n))
    (r5 : Kr * U36 ≤ c5 * (W * n)) (r6 : Kr * Kr ^ 2 ≤ W * n) (r7 : Kr * (C₀ * Kr ^ 2 * Lc) ≤ c7 * (W * n)) (r8 : Kr * R1 ≤ c8 * (W * n))
    (r9 : Kr * Rx ≤ c9 * (W * n)) (rU : Ubr ≤ M + U36) (rL : lam * Kr ^ 3 ≤ Kr ^ 3 + Kr * Ubr + gP)
    (hr : nd ≤ e * Kr ^ 2 * lam + C₀ * Kr ^ 2 * Lg) (hlog : Lg ≤ Lc) :
    T1 + T2 + T3 + nd + R1 + Rx ≤ e * M + (c1 + c2 + c3 + c4 + c5 + 1 + c7 + c8 + c9) * A * (n * e) := by
  have e1 : Kr * (gP / Kr) = gP := by field_simp
  have hl2 : Kr ^ 2 * lam ≤ Kr ^ 2 + Ubr + gP / Kr := by
    have g1 : Kr * (Kr ^ 2 * lam) ≤ Kr * (Kr ^ 2 + Ubr + gP / Kr) := by
      calc Kr * (Kr ^ 2 * lam) = lam * Kr ^ 3 := by ring
        _ ≤ Kr ^ 3 + Kr * Ubr + gP := rL
        _ = Kr * (Kr ^ 2 + Ubr + gP / Kr) := by rw [mul_add, mul_add, e1]; ring
    exact le_of_mul_le_mul_left g1 hKr
  have hgK0 : 0 ≤ gP / Kr := div_nonneg hgP0 hKr.le
  have hK2 : 0 ≤ Kr ^ 2 := by positivity
  have hnd : nd ≤ e * M + (Kr ^ 2 + U36 + gP / Kr + C₀ * Kr ^ 2 * Lc) := by
    have a1 : e * Kr ^ 2 * lam ≤ e * (Kr ^ 2 + (M + U36) + gP / Kr) := by
      calc e * Kr ^ 2 * lam = e * (Kr ^ 2 * lam) := by ring
        _ ≤ e * (Kr ^ 2 + Ubr + gP / Kr) := mul_le_mul_of_nonneg_left hl2 he0.le
        _ ≤ e * (Kr ^ 2 + (M + U36) + gP / Kr) := mul_le_mul_of_nonneg_left (by linarith) he0.le
    have a2 : e * (Kr ^ 2 + U36 + gP / Kr) ≤ 1 * (Kr ^ 2 + U36 + gP / Kr) := mul_le_mul_of_nonneg_right he1 (by linarith)
    have a3 : C₀ * Kr ^ 2 * Lg ≤ C₀ * Kr ^ 2 * Lc := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC0 hK2)
    have e2 : e * (Kr ^ 2 + (M + U36) + gP / Kr) = e * M + e * (Kr ^ 2 + U36 + gP / Kr) := by ring
    linarith
  obtain ⟨X, hX⟩ : ∃ X, X = T1 + T2 + T3 + (Kr ^ 2 + U36 + gP / Kr + C₀ * Kr ^ 2 * Lc) + R1 + Rx := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = c1 + c2 + c3 + c4 + c5 + 1 + c7 + c8 + c9 := ⟨_, rfl⟩
  have hcc0 : 0 ≤ cc := by rw [hcc]; linarith
  have hKX : Kr * X ≤ cc * (W * n) := by
    have e3 : Kr * X = Kr * T1 + Kr * T2 + Kr * T3 + (Kr * Kr ^ 2 + Kr * U36 + Kr * (gP / Kr) + Kr * (C₀ * Kr ^ 2 * Lc)) + Kr * R1 + Kr * Rx := by
      rw [hX]; ring
    have e4 : cc * (W * n) = c1 * (W * n) + c2 * (W * n) + c3 * (W * n) + c4 * (W * n) + c5 * (W * n) + W * n + c7 * (W * n) + c8 * (W * n) + c9 * (W * n) := by
      rw [hcc]; ring
    rw [e3, e4, e1]
    linarith
  have hXle : X ≤ cc * A * (n * e) := by
    have g1 : Kr * X ≤ Kr * (cc * A * (n * e)) := by
      calc Kr * X ≤ cc * (W * n) := hKX
        _ ≤ cc * (A * Kr * e * n) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM hn0) hcc0
        _ = Kr * (cc * A * (n * e)) := by ring
    exact le_of_mul_le_mul_left g1 hKr
  rw [← hcc]
  rw [hX] at hXle
  linarith
end RecursionToBound
