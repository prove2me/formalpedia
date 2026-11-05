-- Prove2me | solution 1 for PaddedDescent.F.Arith.count_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:38.4296+00:00
-- url     : https://prove2.me/submissions/16b12510-43e2-49d8-8b0a-c62f128c5c0b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution {cnt lam Rr L K2 G T : ℕ} (c1 : lam + 1 ≤ 2 ^ L) (O5 : Rr ≤ G) (O8c : 2 * K2 ≤ G)
    (h4 : cnt * 2 ^ (L * (2 * G)) ≤ T) : cnt * (lam + 1) ^ Rr * 2 ^ (L * (2 * K2)) ≤ T := by
  have c2 : (lam + 1) ^ Rr ≤ 2 ^ (L * G) := by
    calc (lam + 1) ^ Rr ≤ (2 ^ L) ^ Rr := Nat.pow_le_pow_left c1 _
      _ ≤ (2 ^ L) ^ G := Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num)) O5
      _ = 2 ^ (L * G) := by rw [← pow_mul]
  calc cnt * (lam + 1) ^ Rr * 2 ^ (L * (2 * K2)) ≤ cnt * 2 ^ (L * G) * 2 ^ (L * G) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ c2)
          (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ O8c))
    _ = cnt * 2 ^ (L * (2 * G)) := by rw [mul_assoc, ← pow_add]; congr 2; ring
    _ ≤ T := h4
end PaddedDescent.F.Arith
