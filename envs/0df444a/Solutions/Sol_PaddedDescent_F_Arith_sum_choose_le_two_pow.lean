-- Prove2me | solution 1 for PaddedDescent.F.Arith.sum_choose_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:59:38.66578+00:00
-- url     : https://prove2.me/submissions/9d087523-9dc3-420a-b355-81571d839643

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Choice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_PaddedDescent_F_ArithWalk
import Theorems.Thm_PaddedDescent_tauOf_works
import Theorems.Thm_PaddedDescent_two_le_tauOf
import Theorems.Thm_WidthK_stLeafCount


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
namespace PaddedDescent.F.Arith
theorem _root_.solution {k s : ℕ} (hs : s0K k ≤ s) (n : ℕ) :
    ∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j ≤ 2 ^ (n / 2 ^ s + 1) := by
  have h1 := WidthK.stLeafCount k (tauOf s) (1 / 2 ^ s) (le_trans (by norm_num) (two_le_tauOf s)) (tauOf_works hs) n
  have h2 : n < 2 ^ s * (n / 2 ^ s + 1) := Nat.lt_mul_div_succ n (by positivity)
  have h3 : (n : ℝ) ≤ (2 : ℝ) ^ s * ((n / 2 ^ s + 1 : ℕ) : ℝ) := by exact_mod_cast h2.le
  have h4 : (1 : ℝ) / 2 ^ s * (n : ℝ) ≤ ((n / 2 ^ s + 1 : ℕ) : ℝ) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    rw [one_div, inv_mul_le_iff₀ hp]
    exact h3
  have h5 : ((∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j : ℕ) : ℝ)
      ≤ ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by
    calc ((∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (1 / 2 ^ s * (n : ℝ)) := h1
      _ ≤ (2 : ℝ) ^ (((n / 2 ^ s + 1 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
      _ = ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
  exact_mod_cast h5
end PaddedDescent.F.Arith
