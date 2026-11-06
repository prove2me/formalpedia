-- Prove2me | solution 1 for SparsificationLemma.Geo.works_of_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:40:34.14539+00:00
-- url     : https://prove2.me/submissions/82f9337e-acf0-4a5b-a3eb-924c464f40be

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Geo_Defs
import Definitions.Def_SparsificationLemma_Geo_Tau
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Geo_Eps
import Theorems.Thm_SparsificationLemma_Geo_log_le_mul_log_two
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Geo
open UniformInK
namespace SparsificationLemma.Geo
theorem _root_.solution {k : ℕ} {ε X T : ℝ} (hk : 1 ≤ (k : ℝ)) (h0 : 0 < ε) (h1 : ε ≤ 1) (hX : (k : ℝ) = ε * X / 8)
    (hlo : X ^ 3 ≤ T) (hhi : T ≤ (9 * X / 8) ^ 3) :
    ((k : ℝ) / T) * Real.logb 2 (Real.exp 1 * T * T ^ (2 * k)) ≤ ε := by
  have hX8 : 8 ≤ X := by nlinarith
  have hX0 : 0 < X := by linarith
  have hX3 : 0 < X ^ 3 := by positivity
  have hT0 : 0 < T := by linarith
  have hL1 := Real.log_two_gt_d9
  have hL0 : 0 < Real.log 2 := by linarith
  have hlogT : Real.log T ≤ 27 * X / 8 * Real.log 2 := by
    have a1 : Real.log T ≤ Real.log ((9 * X / 8) ^ 3) := Real.log_le_log hT0 hhi
    rw [Real.log_pow] at a1
    have a2 := log_le_mul_log_two (y := 9 * X / 8) (by positivity)
    push_cast at a1
    linarith
  have hlog : Real.log (Real.exp 1 * T * T ^ (2 * k)) = 1 + (2 * (k : ℝ) + 1) * Real.log T := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (Real.exp_pos 1).ne' hT0.ne', Real.log_exp, Real.log_pow]
    push_cast; ring
  have hW : Real.logb 2 (Real.exp 1 * T * T ^ (2 * k)) ≤ 11 * (k : ℝ) * X := by
    rw [Real.logb, div_le_iff₀ hL0, hlog]
    have b1 : (2 * (k : ℝ) + 1) * Real.log T ≤ (2 * (k : ℝ) + 1) * (27 * X / 8 * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogT (by linarith)
    have b2 : 2 + (2 * (k : ℝ) + 1) * (27 * X / 8) ≤ 11 * (k : ℝ) * X := by nlinarith
    have b3 := mul_le_mul_of_nonneg_right b2 hL0.le
    nlinarith
  have hkT : 0 ≤ (k : ℝ) / T := by positivity
  refine (mul_le_mul_of_nonneg_left hW hkT).trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hT0]
  have c1 : (k : ℝ) * (11 * (k : ℝ) * X) = 11 / 64 * ε ^ 2 * X ^ 3 := by rw [hX]; ring
  rw [c1]
  have c2 : 11 / 64 * ε ^ 2 ≤ ε := by nlinarith
  calc 11 / 64 * ε ^ 2 * X ^ 3 ≤ ε * X ^ 3 := mul_le_mul_of_nonneg_right c2 hX3.le
    _ ≤ ε * T := mul_le_mul_of_nonneg_left hlo h0.le
end SparsificationLemma.Geo
