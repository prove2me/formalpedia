-- Prove2me | solution 1 for OccurM.back_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:15:33.789469+00:00
-- url     : https://prove2.me/submissions/c0675677-972c-415a-bea7-4bfb7a41648a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_OccurM_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_Wrap_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OccurM_ArithBack
import Theorems.Thm_OccurM_lg_mul_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_OccurM_expClauses_le
import Theorems.Thm_OccurM_one_le_expClauses


set_option autoImplicit false
section
section
open OccurM
open MainTheoremForms ClausesOccur VariableBound.Paper
variable {α : ℝ} {k m : ℕ}
namespace OccurM
theorem _root_.solution (h0 : 0 ≤ α) (h1 : α ≤ 1) (C : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) {a : ℕ} (ha : a ≤ 8 * (k * m) ^ 2) :
    timeClauses α C k m + C * a ^ C ≤ SatM.bound (SatM.rPow α) (650 * C + 1) k m := by
  have hX := one_le_expClauses h0 h1 hk hm
  have hXY := expClauses_le h0 h1 k hm
  have hlg := lg_mul_le h1 hk hm
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  set Y : ℝ := (k : ℝ) * m * SatM.rPow α m with hY
  have hY0 : 0 ≤ Y := by linarith
  have hs2 : 2 ≤ k * m := by nlinarith
  have hs0 : (0 : ℝ) < (k : ℝ) * m := by exact_mod_cast (by omega : 0 < k * m)
  have ha5 : a ≤ (k * m) ^ 5 := by
    calc a ≤ 2 ^ 3 * (k * m) ^ 2 := ha
      _ ≤ (k * m) ^ 3 * (k * m) ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hs2 3)
      _ = (k * m) ^ 5 := by ring
  have hbig : ∀ t : ℝ, t ≤ (650 * C + 1) * Y → (2 : ℝ) ^ t ≤ (2 : ℝ) ^ ((650 * (C : ℝ) + 1) * Y) := fun t ht => Real.rpow_le_rpow_of_exponent_le one_le_two ht
  have ht : ((timeClauses α C k m : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((650 * (C : ℝ) + 1) * Y) := by
    unfold timeClauses
    refine (Nat.floor_le (by positivity)).trans (hbig _ ?_)
    nlinarith [mul_le_mul_of_nonneg_left hXY hC0, mul_nonneg hC0 hY0]
  have hpw : ((a : ℝ)) ^ C ≤ (2 : ℝ) ^ ((650 * (C : ℝ) + 1) * Y) := by
    have h5 : (a : ℝ) ≤ ((k : ℝ) * m) ^ 5 := by exact_mod_cast ha5
    have e2 : ((k : ℝ) * m) = (2 : ℝ) ^ lg ((k : ℝ) * m) := by
      unfold lg
      rw [Real.rpow_logb two_pos (by norm_num) hs0]
    calc (a : ℝ) ^ C ≤ (((k : ℝ) * m) ^ 5) ^ C := pow_le_pow_left₀ (Nat.cast_nonneg a) h5 C
      _ = ((k : ℝ) * m) ^ (5 * C) := (pow_mul _ _ _).symm
      _ = ((2 : ℝ) ^ lg ((k : ℝ) * m)) ^ (5 * C) := by rw [← e2]
      _ = (2 : ℝ) ^ (lg ((k : ℝ) * m) * ((5 * C : ℕ) : ℝ)) := (Real.rpow_mul_natCast two_pos.le _ _).symm
      _ ≤ _ := hbig _ (by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right hlg hC0, mul_nonneg hC0 hY0])
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ ((650 * (C : ℝ) + 1) * Y) := by positivity
  unfold SatM.bound
  refine Nat.le_floor ?_
  have e : (((650 * C + 1 : ℕ) : ℝ)) * k * m * SatM.rPow α m = (650 * (C : ℝ) + 1) * Y := by
    rw [hY]
    push_cast
    ring
  rw [e]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hpw hC0, mul_nonneg hC0 hp0.le]
end OccurM
