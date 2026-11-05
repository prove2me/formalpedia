-- Prove2me | solution 1 for Wrap.Arith.lg_le_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:55:10.40353+00:00
-- url     : https://prove2.me/submissions/7150ffe1-6e6f-4af0-8e57-988f275c03c2

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
import Theorems.Thm_Wrap_Arith_lg_add_four_facts
import Theorems.Thm_Wrap_Arith_lg_le_fourth_root


set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith
namespace Wrap.Arith
theorem _root_.solution (n : ℕ) : lg ((n : ℝ) + 4) ≤ 64 * ((n : ℝ) * SatK.rN 1 (1 / 2) n) + 256 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hN : (0 : ℝ) < (n : ℝ) + 4 := by positivity
  obtain ⟨h2, hl⟩ := lg_add_four_facts n
  have hroot := lg_le_fourth_root hN
  rw [rate_eq]
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = lg ((n : ℝ) + 4) := ⟨_, rfl⟩
  rw [← hΛ] at h2 hl hroot ⊢
  have hv1 : 1 ≤ Real.sqrt ((n : ℝ) + 4) := Real.one_le_sqrt.2 (by linarith)
  have hvv : Real.sqrt ((n : ℝ) + 4) * Real.sqrt ((n : ℝ) + 4) = (n : ℝ) + 4 := Real.mul_self_sqrt hN.le
  have hww : Real.sqrt (Real.sqrt ((n : ℝ) + 4)) * Real.sqrt (Real.sqrt ((n : ℝ) + 4)) = Real.sqrt ((n : ℝ) + 4) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hsq : Λ * Λ ≤ 64 * ((n : ℝ) + 4) := by
    have h3 : Λ * Λ ≤ (8 * Real.sqrt (Real.sqrt ((n : ℝ) + 4))) * (8 * Real.sqrt (Real.sqrt ((n : ℝ) + 4))) := mul_self_le_mul_self (by linarith) hroot
    have h4 : Real.sqrt ((n : ℝ) + 4) ≤ (n : ℝ) + 4 := by nlinarith
    nlinarith
  have hs1 : 1 ≤ Real.sqrt Λ := Real.one_le_sqrt.2 (by linarith)
  have hs0 : 0 < Real.sqrt Λ := by linarith
  have hss : Real.sqrt Λ * Real.sqrt Λ = Λ := Real.mul_self_sqrt (by linarith)
  have a1 : Λ * Real.sqrt Λ ≤ 64 * ((n : ℝ) + 4) := by
    have h5 : Real.sqrt Λ ≤ Λ := by nlinarith
    have h6 : Λ * Real.sqrt Λ ≤ Λ * Λ := mul_le_mul_of_nonneg_left h5 (by linarith)
    linarith
  have a2 : Λ ≤ 64 * ((n : ℝ) + 4) / Real.sqrt Λ := (le_div_iff₀ hs0).2 a1
  have a3 : 64 * ((n : ℝ) + 4) / Real.sqrt Λ = 64 * ((n : ℝ) / Real.sqrt Λ) + 256 / Real.sqrt Λ := by ring
  have a4 : 256 / Real.sqrt Λ ≤ 256 := div_le_self (by norm_num) hs1
  have a5 : (n : ℝ) / Real.sqrt Λ ≤ (n : ℝ) * (lg Λ / Real.sqrt Λ) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hn0 hl) hs0.le
  linarith
end Wrap.Arith
