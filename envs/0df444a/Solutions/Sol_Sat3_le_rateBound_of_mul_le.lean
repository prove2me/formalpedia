-- Prove2me | solution 1 for Sat3.le_rateBound_of_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:39:35.565823+00:00
-- url     : https://prove2.me/submissions/d0e64c5a-48f5-477a-a5b1-b6e9a9c39bf2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_PaddedDescent_Params
import Definitions.Def_ToTuring_EndLemmas
import Definitions.Def_PaddedDescent_RateLemmas
import Theorems.Thm_Sat3_le_rateBound_of_real

set_option autoImplicit false
section
section
open Sat3
open Turing
open scoped NNReal ENNReal
namespace Sat3
theorem _root_.solution {p q b A C₁ s e n : ℕ} (hq : 0 < q)
    (hs : p * (Nat.log2 (Nat.log2 n) + 2) ≤ q * (s + b)) (he : e * 2 ^ s ≤ C₁ * (n + 2 ^ s)) :
    A * 2 ^ e ≤ rateBound (A * 2 ^ C₁ + C₁ * 2 ^ b) ((p : ℝ) / q) n := by
  apply le_rateBound_of_real hq hs
  have he' : (e : ℝ) * 2 ^ s ≤ C₁ * (n + 2 ^ s) := by exact_mod_cast he
  have h1 : (e : ℝ) ≤ (C₁ : ℝ) * n / 2 ^ s + C₁ := by
    rw [← le_div_iff₀ (by positivity)] at he'
    refine he'.trans_eq ?_
    field_simp
  push_cast
  rw [← Real.rpow_natCast 2 e]
  gcongr
  exact one_le_two
end Sat3
