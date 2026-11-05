-- Prove2me | solution 1 for PaddedDescent.F.Arith.lamNext_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:58:10.202328+00:00
-- url     : https://prove2.me/submissions/d1a901b2-d69a-4b06-b9ea-c3b74f823848

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

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (K g lam : ℕ) :
    Dcol * (K ^ 2 * lamNext K g lam) ≤ Dcol * Ubar g lam + 3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam) + Dcol * K ^ 2 := by
  have h := Nat.div_mul_le_self (Dcol * Ubar g lam + 3 * g ^ 2 * capM g lam) (Dcol * K ^ 2)
  have e : 3 * g ^ 2 * capM g lam = 3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam) := by unfold capM; ring
  rw [e] at h
  unfold lamNext
  rw [e]
  calc Dcol * (K ^ 2 * ((Dcol * Ubar g lam + (3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam))) / (Dcol * K ^ 2) + 1))
      = (Dcol * Ubar g lam + (3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam))) / (Dcol * K ^ 2) * (Dcol * K ^ 2) + Dcol * K ^ 2 := by ring
    _ ≤ Dcol * Ubar g lam + 3 * (g ^ 3 * lam) + 6 * (g ^ 4 * lam) + Dcol * K ^ 2 := by omega
end PaddedDescent.F.Arith
