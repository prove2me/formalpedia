-- Prove2me | solution 1 for PaddedDescent.F.Arith.lamNext_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:34.569047+00:00
-- url     : https://prove2.me/submissions/b545b61e-39c9-44f3-abf5-5a29e974ef3e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithLevel
import Theorems.Thm_PaddedDescent_F_Arith_mul_Ubar_le
import Theorems.Thm_PaddedDescent_F_Arith_lamNext_mul_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {K g : ℕ} (hg : K ≤ g) (hg20 : 2 ^ 20 ≤ g) (lam : ℕ) :
    10000 * (K ^ 2 * lamNext K g lam) ≤ 8963 * (g ^ 4 * lam) + 10000 * g ^ 4 := by
  have h0 := lamNext_mul_le K g lam
  have h1 := mul_Ubar_le g lam
  have hD : Dcol = 262144 := by norm_num [Dcol]
  rw [hD] at h0
  have f1 : 2 ^ 20 * (g ^ 3 * lam) ≤ g ^ 4 * lam := by
    calc 2 ^ 20 * (g ^ 3 * lam) ≤ g * (g ^ 3 * lam) := Nat.mul_le_mul_right _ hg20
      _ = g ^ 4 * lam := by ring
  have f3 : 4 * (K ^ 2 + 1) ≤ g ^ 4 := by
    have a1 : K ^ 2 ≤ g ^ 2 := Nat.pow_le_pow_left hg 2
    have a2 : 8 ≤ g ^ 2 := by nlinarith
    have a3 : 8 * g ^ 2 ≤ g ^ 2 * g ^ 2 := Nat.mul_le_mul_right _ a2
    have a4 : g ^ 2 * g ^ 2 = g ^ 4 := by ring
    omega
  norm_num at f1
  omega
end PaddedDescent.F.Arith
