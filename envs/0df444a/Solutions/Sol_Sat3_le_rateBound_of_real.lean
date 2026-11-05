-- Prove2me | solution 1 for Sat3.le_rateBound_of_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:37:49.75476+00:00
-- url     : https://prove2.me/submissions/6874bcd8-6bad-4136-92b3-f77511039a00

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
import Theorems.Thm_Sat3_logb_rpow_pos
import Theorems.Thm_Sat3_logb_rpow_le_two_pow

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution {p q b A C₁ s n t : ℕ} (hq : 0 < q) (hs : p * (Nat.log2 (Nat.log2 n) + 2) ≤ q * (s + b))
    (ht : (t : ℝ) ≤ A * (2 : ℝ) ^ ((C₁ : ℝ) * n / 2 ^ s + C₁)) :
    t ≤ rateBound (A * 2 ^ C₁ + C₁ * 2 ^ b) ((p : ℝ) / q) n := by
  unfold rateBound
  apply Nat.le_floor
  refine ht.trans ?_
  have hLpos := logb_rpow_pos n ((p : ℝ) / q)
  have hL := logb_rpow_le_two_pow hq hs
  generalize Real.logb 2 ((n : ℝ) + 2) ^ ((p : ℝ) / q) = L at hLpos hL ⊢
  have hA : (0 : ℝ) ≤ (A : ℝ) * 2 ^ C₁ := by positivity
  have hB : (0 : ℝ) ≤ (C₁ : ℝ) * 2 ^ b := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (C₁ : ℝ) * n / 2 ^ s ≤ (C₁ * 2 ^ b) * n / L := by
    calc (C₁ : ℝ) * n / 2 ^ s = (C₁ * 2 ^ b) * n / 2 ^ (s + b) := by
          rw [pow_add]
          field_simp
      _ ≤ (C₁ * 2 ^ b) * n / L := div_le_div_of_nonneg_left (by positivity) hLpos hL
  push_cast
  calc (A : ℝ) * (2 : ℝ) ^ ((C₁ : ℝ) * n / 2 ^ s + C₁)
      = (A * 2 ^ C₁) * (2 : ℝ) ^ ((C₁ : ℝ) * n / 2 ^ s) := by
        rw [Real.rpow_add two_pos, Real.rpow_natCast]
        ring
    _ ≤ (A * 2 ^ C₁ + C₁ * 2 ^ b) * (2 : ℝ) ^ ((A * 2 ^ C₁ + C₁ * 2 ^ b) * n / L) := by
      apply mul_le_mul (by linarith) _ (by positivity) (by linarith)
      apply Real.rpow_le_rpow_of_exponent_le one_le_two
      refine h1.trans ?_
      apply div_le_div_of_nonneg_right _ hLpos.le
      apply mul_le_mul_of_nonneg_right (by linarith) hn
end Sat3
