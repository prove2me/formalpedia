-- Prove2me | solution 1 for Sat3.logb_rpow_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:36:01.415057+00:00
-- url     : https://prove2.me/submissions/82258b1f-62b1-4fe0-b3dc-fe53bb2c0a9a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
import Theorems.Thm_Sat3_one_le_logb
import Theorems.Thm_Sat3_logb_le_two_pow

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution {p q b s n : ℕ} (hq : 0 < q) (hs : p * (Nat.log2 (Nat.log2 n) + 2) ≤ q * (s + b)) :
    Real.logb 2 ((n : ℝ) + 2) ^ ((p : ℝ) / q) ≤ (2 : ℝ) ^ (s + b) := by
  have hL := one_le_logb n
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hs' : (p : ℝ) * ((Nat.log2 (Nat.log2 n) + 2 : ℕ) : ℝ) ≤ q * ((s + b : ℕ) : ℝ) := by exact_mod_cast hs
  calc Real.logb 2 ((n : ℝ) + 2) ^ ((p : ℝ) / q)
      ≤ ((2 : ℝ) ^ (Nat.log2 (Nat.log2 n) + 2)) ^ ((p : ℝ) / q) :=
        Real.rpow_le_rpow (by linarith) (logb_le_two_pow n) (by positivity)
    _ = (2 : ℝ) ^ (((Nat.log2 (Nat.log2 n) + 2 : ℕ) : ℝ) * ((p : ℝ) / q)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two]
    _ ≤ (2 : ℝ) ^ ((s + b : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le one_le_two
        rw [mul_div_assoc', div_le_iff₀ hq']
        linarith
    _ = (2 : ℝ) ^ (s + b) := Real.rpow_natCast _ _
end Sat3
