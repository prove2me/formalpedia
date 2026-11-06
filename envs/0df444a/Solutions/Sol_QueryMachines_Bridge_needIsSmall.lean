-- Prove2me | solution 1 for QueryMachines.Bridge.needIsSmall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:32.188343+00:00
-- url     : https://prove2.me/submissions/b5a95896-63fe-4b44-a6e5-d3bed54df86b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_CountedToPadded_Need
import Theorems.Thm_QueryMachines_Bridge_Proof_den_pos
import Theorems.Thm_QueryMachines_Bridge_Proof_ceilMul_le
import Theorems.Thm_QueryMachines_Bridge_Proof_size_le_log
import Theorems.Thm_QueryMachines_Bridge_Proof_needOf_eq

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork PaddedDescent.F Printed CliqueLevels Proof
namespace QueryMachines.Bridge
theorem _root_.solution : NeedIsSmall := by
  intro K e C₀ num hL hN l lam B hlam hB
  rw [needOf_eq]
  push_cast
  have h1 := ceilMul_le (a := (num (unary l, unary (K l))).1) (den_pos hL hN l) (K l ^ 2 * lam)
  generalize ceilMul (num (unary l, unary (K l))).1 (num (unary l, unary (K l))).2 (K l ^ 2 * lam) = c at h1 ⊢
  have hK : (2 : ℝ) ≤ K l := by exact_mod_cast hL.K_two l
  have hl1 : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hx : (4 : ℝ) ≤ (K l : ℝ) * ((lam : ℝ) + B) := by nlinarith
  have hL2 : 2 ≤ Real.logb 2 ((K l : ℝ) * ((lam : ℝ) + B)) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith)]
    have : (2 : ℝ) ^ (2 : ℝ) = 4 := by rw [show (2 : ℝ) ^ (2 : ℝ) = (2 : ℝ) ^ ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [this]; exact hx
  have hm : 1 ≤ K l * (lam + B + 1) := Nat.mul_pos (by have := hL.K_two l; omega) (by omega)
  have h2 := size_le_log hm
  have h3 : Real.logb 2 ((K l * (lam + B + 1) : ℕ) : ℝ) ≤ Real.logb 2 ((K l : ℝ) * ((lam : ℝ) + B)) + 1 := by
    have h4 : ((K l * (lam + B + 1) : ℕ) : ℝ) ≤ 2 * ((K l : ℝ) * ((lam : ℝ) + B)) := by push_cast; nlinarith
    have h5 : Real.logb 2 (2 * ((K l : ℝ) * ((lam : ℝ) + B))) = 1 + Real.logb 2 ((K l : ℝ) * ((lam : ℝ) + B)) := by
      rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one one_lt_two]
    have h6 := Real.logb_le_logb_of_le one_lt_two (by exact_mod_cast hm) h4
    linarith
  generalize Real.logb 2 ((K l : ℝ) * ((lam : ℝ) + B)) = L at *
  generalize (Nat.size (K l * (lam + B + 1)) : ℝ) = s at *
  have hs : s ≤ L + 2 := by linarith
  unfold cutNumber
  push_cast at h1 ⊢
  have hC : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
  have hP : (4 : ℝ) ≤ (K l : ℝ) ^ 2 := by nlinarith
  have hCP : 0 ≤ (C₀ : ℝ) * (K l : ℝ) ^ 2 := by positivity
  have g1 : (C₀ : ℝ) * (K l : ℝ) ^ 2 * s ≤ (C₀ : ℝ) * (K l : ℝ) ^ 2 * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hCP
  have g2 : (3 : ℝ) ≤ (K l : ℝ) ^ 2 * L := by nlinarith
  linarith
end QueryMachines.Bridge
