-- Prove2me | solution 1 for P2M_ClauseBound_TopN_End_time_le__345fca42d669
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:28:35.087684+00:00
-- url     : https://prove2.me/submissions/8429fa2c-721b-4e58-a419-bb952a69df4f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_WidthK_Decode
import Definitions.Def_CountKSat_InOut
import Definitions.Def_ClauseBound_TopN_End
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End
namespace ClauseBound.TopN.End
theorem _root_.solution (q L E a H G : ℕ) {X : ℝ} (hX : 0 ≤ X) (hL : ((L + 1 : ℕ) : ℝ) ≤ (a : ℝ) * (2 : ℝ) ^ ((H : ℝ) * X)) (hE : (E : ℝ) ≤ (G : ℝ) * X) :
    ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) ≤
      ((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) * (2 : ℝ) ^ (((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) * X) := by
  have e2 : ((2 : ℝ) ^ E) ≤ (2 : ℝ) ^ ((G : ℝ) * X) := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
  have m1 : (2 : ℝ) ^ ((H : ℝ) * X) ≤ (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right _ _) hX)
  have m2 : (2 : ℝ) ^ ((G : ℝ) * X) ≤ (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left _ _) hX)
  have h3 : ((L + 2 ^ E + 1 : ℕ) : ℝ) ≤ ((a + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) := by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    calc ((L + 2 ^ E + 1 : ℕ) : ℝ) = ((L + 1 : ℕ) : ℝ) + (2 : ℝ) ^ E := by push_cast; ring
      _ ≤ (a : ℝ) * (2 : ℝ) ^ ((H : ℝ) * X) + (2 : ℝ) ^ ((G : ℝ) * X) := add_le_add hL e2
      _ ≤ (a : ℝ) * (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) + (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) := add_le_add (mul_le_mul_of_nonneg_left m1 ha0) m2
      _ = ((a + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) := by push_cast; ring
  have h4 : ((2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X)) ^ q = (2 : ℝ) ^ (((q * (H + G) : ℕ) : ℝ) * X) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
  have h5 : (2 : ℝ) ^ (((q * (H + G) : ℕ) : ℝ) * X) ≤ (2 : ℝ) ^ (((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) * X) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right ?_ hX)
    exact_mod_cast Nat.le_add_left _ _
  have h6 : ((q * (a + 1) ^ q : ℕ) : ℝ) ≤ ((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
  calc ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) = (q : ℝ) * ((L + 2 ^ E + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (((a + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X)) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 q) (by positivity)
    _ = ((q * (a + 1) ^ q : ℕ) : ℝ) * (2 : ℝ) ^ (((q * (H + G) : ℕ) : ℝ) * X) := by rw [mul_pow, h4]; push_cast; ring
    _ ≤ _ := mul_le_mul h6 h5 (by positivity) (by positivity)
end ClauseBound.TopN.End
