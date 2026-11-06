-- Prove2me | solution 1 for PairsToBound.steps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:49:17.308933+00:00
-- url     : https://prove2.me/submissions/768684df-cb06-4238-a682-ba181d8ca98c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PairsToBound_Width
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_Decode
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSatRate_Brute
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_CountKSatRate_Pad
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_PairsToBound_Exhaust
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open PairsToBound
open Turing Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg Wrap MainTheoremForms
open Sat3 (CNF)
namespace PairsToBound
theorem _root_.solution (q : ℕ) {k n L : ℕ} (hk : 1 ≤ k) (hn : 2 ≤ n) (hL : L + 1 ≤ n ^ (8 * k)) : q * (L + 2 ^ n + 1) ^ q ≤ 2 ^ (8 * q * n) * n ^ (8 * q * k) := by
  have hA : 2 ≤ n ^ (8 * k) := hn.trans (Nat.le_self_pow (by omega) n)
  have hB : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have h1 : L + 2 ^ n + 1 ≤ n ^ (8 * k) * 2 ^ n := le_trans (by omega) (Nat.add_le_mul hA hB)
  have h2 : q * 1 ≤ q * n := Nat.mul_le_mul_left q (by omega)
  calc q * (L + 2 ^ n + 1) ^ q ≤ 2 ^ q * (n ^ (8 * k) * 2 ^ n) ^ q := Nat.mul_le_mul (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left h1 q)
    _ = 2 ^ (q + n * q) * n ^ (8 * q * k) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]
      ring
    _ ≤ 2 ^ (8 * q * n) * n ^ (8 * q * k) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
end PairsToBound
