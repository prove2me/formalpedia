-- Prove2me | solution 1 for QueryMachines.Bridge.needSuffices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:04:45.455079+00:00
-- url     : https://prove2.me/submissions/56980aa2-8a1e-42ba-b634-74824e97a33e

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
import Theorems.Thm_QueryMachines_Bridge_Proof_le_ceilMul
import Theorems.Thm_QueryMachines_Bridge_Proof_needOf_eq

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge
open Groundwork PaddedDescent.F Printed CliqueLevels Proof
namespace QueryMachines.Bridge
theorem _root_.solution : NeedSuffices := by
  intro K e C₀ num hL hN l lam B _
  rw [needOf_eq]
  have h1 := le_ceilMul (a := (num (unary l, unary (K l))).1) (den_pos hL hN l) (K l ^ 2 * lam)
  generalize ceilMul (num (unary l, unary (K l))).1 (num (unary l, unary (K l))).2 (K l ^ 2 * lam) = c at h1 ⊢
  have h2 : (2 : ℝ) ^ (cutNumber K num l * (K l : ℝ) ^ 2 * lam) ≤ (2 : ℝ) ^ c := by
    rw [← Real.rpow_natCast (2 : ℝ) c]
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    unfold cutNumber
    push_cast at h1
    linarith
  have h3 : ((K l : ℝ) * ((lam : ℝ) + ((B + 1 : ℕ) : ℝ))) ^ (C₀ * K l ^ 2) ≤ (2 : ℝ) ^ (C₀ * K l ^ 2 * Nat.size (K l * (lam + B + 1))) := by
    have h4 : K l * (lam + B + 1) ≤ 2 ^ Nat.size (K l * (lam + B + 1)) := (Nat.lt_size_self _).le
    have h5 : (K l : ℝ) * ((lam : ℝ) + ((B + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ Nat.size (K l * (lam + B + 1)) := by
      have : ((K l * (lam + B + 1) : ℕ) : ℝ) ≤ ((2 ^ Nat.size (K l * (lam + B + 1)) : ℕ) : ℝ) := Nat.cast_le.2 h4
      push_cast at this ⊢
      linarith
    calc _ ≤ ((2 : ℝ) ^ Nat.size (K l * (lam + B + 1))) ^ (C₀ * K l ^ 2) := pow_le_pow_left₀ (by positivity) h5 _
      _ = _ := by rw [← pow_mul, Nat.mul_comm]
  unfold bound
  calc 4 * ((2 : ℝ) ^ (cutNumber K num l * (K l : ℝ) ^ 2 * lam) * ((K l : ℝ) * ((lam : ℝ) + ((B + 1 : ℕ) : ℝ))) ^ (C₀ * K l ^ 2))
      ≤ 4 * ((2 : ℝ) ^ c * (2 : ℝ) ^ (C₀ * K l ^ 2 * Nat.size (K l * (lam + B + 1)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (by positivity) (by positivity)) (by norm_num)
    _ = (2 : ℝ) ^ (c + C₀ * K l ^ 2 * Nat.size (K l * (lam + B + 1)) + 2) := by rw [pow_add, pow_add]; ring
end QueryMachines.Bridge
