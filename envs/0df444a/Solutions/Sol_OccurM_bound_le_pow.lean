-- Prove2me | solution 1 for OccurM.bound_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:10:11.416496+00:00
-- url     : https://prove2.me/submissions/e81c351f-b7ce-4662-b5e1-55dc108d9715

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_Time
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OccurM_Arith
import Theorems.Thm_OccurM_one_le_expClauses
import Theorems.Thm_OccurM_shift_le
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (h0 : 0 ≤ α) (h1 : α ≤ 1) (C : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) :
    ∃ E : ℕ, SatM.bound (SatM.rPow α) C k m ≤ 2 ^ E ∧ (E : ℝ) ≤ ((2 * C + 1 : ℕ) : ℝ) * expClauses α k m := by
  have hX := one_le_expClauses h0 h1 hk hm
  have hs := shift_le h0 k hm
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hpos : 0 ≤ (C : ℝ) + C * expClauses α k m := add_nonneg hC0 (mul_nonneg hC0 (by linarith))
  refine ⟨⌈(C : ℝ) + C * expClauses α k m⌉₊, ?_, ?_⟩
  · have hC2 : (C : ℝ) ≤ (2 : ℝ) ^ (C : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.lt_two_pow_self.le
    have e : (C : ℝ) * k * m * SatM.rPow α m = (C : ℝ) * ((k : ℝ) * m * SatM.rPow α m) := by ring
    have hb : ((SatM.bound (SatM.rPow α) C k m : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) + C * expClauses α k m) := by
      unfold SatM.bound
      calc _ ≤ (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * k * m * SatM.rPow α m) := Nat.floor_le (by positivity)
        _ ≤ (2 : ℝ) ^ (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * expClauses α k m) := by
          rw [e]
          exact mul_le_mul hC2 (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hs hC0)) (by positivity) (by positivity)
        _ = _ := (Real.rpow_add two_pos _ _).symm
    have h2 := Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil ((C : ℝ) + C * expClauses α k m))
    rw [Real.rpow_natCast] at h2
    exact_mod_cast hb.trans h2
  · have h := (Nat.ceil_lt_add_one hpos).le
    push_cast
    nlinarith [mul_nonneg hC0 (sub_nonneg.2 hX)]
end OccurM
