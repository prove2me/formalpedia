-- Prove2me | solution 1 for PaddedDescent.padded_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:39:13.685339+00:00
-- url     : https://prove2.me/submissions/22043630-0594-46fe-a637-4f9ba709c323

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_PaddedDescent_RateLemmas
import Definitions.Def_PaddedDescent_PadRate
import Theorems.Thm_PaddedDescent_log2_mul_two_pow_le
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
namespace PaddedDescent
theorem _root_.solution (q C₀ : ℕ) {n s E : ℕ} (hs : 2 ^ s ≤ Nat.log2 (n + 2)) (hE : E * 2 ^ s ≤ C₀ * (n + 2 ^ s)) :
    q * (25 * (n + 2) ^ 4 + 2 ^ E) ^ q ≤ q * 2 ^ (q * (E + 4 * Nat.log2 (n + 2) + 10)) ∧
      q * (E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s ≤ q * (C₀ + 42) * (n + 2 ^ s) := by
  constructor
  · have h2 : (n + 2) ^ 4 ≤ 2 ^ (4 * Nat.log2 (n + 2) + 4) := by
      calc (n + 2) ^ 4 ≤ (2 ^ (Nat.log2 (n + 2) + 1)) ^ 4 := Nat.pow_le_pow_left Nat.lt_log2_self.le 4
        _ = 2 ^ (4 * Nat.log2 (n + 2) + 4) := by rw [← pow_mul]; congr 1; ring
    have h3 : 25 * (n + 2) ^ 4 ≤ 2 ^ (E + 4 * Nat.log2 (n + 2) + 9) := by
      calc 25 * (n + 2) ^ 4 ≤ 2 ^ 5 * 2 ^ (4 * Nat.log2 (n + 2) + 4) := Nat.mul_le_mul (by norm_num) h2
        _ = 2 ^ (4 * Nat.log2 (n + 2) + 9) := by rw [← pow_add]; congr 1; ring
        _ ≤ 2 ^ (E + 4 * Nat.log2 (n + 2) + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2 ^ E ≤ 2 ^ (E + 4 * Nat.log2 (n + 2) + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 25 * (n + 2) ^ 4 + 2 ^ E ≤ 2 ^ (E + 4 * Nat.log2 (n + 2) + 10) := by
      have : 2 ^ (E + 4 * Nat.log2 (n + 2) + 10) = 2 ^ (E + 4 * Nat.log2 (n + 2) + 9) * 2 := pow_succ 2 _
      omega
    calc q * (25 * (n + 2) ^ 4 + 2 ^ E) ^ q ≤ q * (2 ^ (E + 4 * Nat.log2 (n + 2) + 10)) ^ q :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h5 q)
      _ = _ := by rw [← pow_mul, Nat.mul_comm q (E + 4 * Nat.log2 (n + 2) + 10)]
  · have h1 := log2_mul_two_pow_le hs
    have h2 : (E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s ≤ (C₀ + 42) * (n + 2 ^ s) := by
      calc (E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s
          = E * 2 ^ s + 4 * (Nat.log2 (n + 2) * 2 ^ s) + 10 * 2 ^ s := by ring
        _ ≤ C₀ * (n + 2 ^ s) + 4 * (8 * (n + 2 ^ s)) + 10 * (n + 2 ^ s) := by
            have : 2 ^ s ≤ n + 2 ^ s := Nat.le_add_left _ _
            omega
        _ = (C₀ + 42) * (n + 2 ^ s) := by ring
    calc q * (E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s = q * ((E + 4 * Nat.log2 (n + 2) + 10) * 2 ^ s) := Nat.mul_assoc _ _ _
      _ ≤ q * ((C₀ + 42) * (n + 2 ^ s)) := Nat.mul_le_mul_left _ h2
      _ = _ := (Nat.mul_assoc _ _ _).symm
end PaddedDescent
