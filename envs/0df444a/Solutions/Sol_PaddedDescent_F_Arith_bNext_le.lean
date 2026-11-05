-- Prove2me | solution 1 for PaddedDescent.F.Arith.bNext_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:58:11.211699+00:00
-- url     : https://prove2.me/submissions/62613302-bfd3-4302-9388-da2e1f6bfa67

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
theorem _root_.solution {K g : ℕ} (hK : 256 ≤ K) (hg : K ≤ g) (lam B : ℕ) :
    bNext K g lam B ≤ g ^ 3 * B + 2 * (g ^ 4 * lam) := by
  set m := 2 * g / K with hm
  have m1 : m * K ≤ 2 * g := Nat.div_mul_le_self _ _
  have m2 : 128 * m ≤ g := by nlinarith
  have a1 : Pn g lam * m ≤ g ^ 4 * lam := by
    calc Pn g lam * m = 2 * m * (g ^ 3 * lam) := by unfold Pn; ring
      _ ≤ g * (g ^ 3 * lam) := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ 4 * lam := by ring
  have a2 : (m + m * m) * K ≤ g ^ 2 := by
    calc (m + m * m) * K = (1 + m) * (m * K) := by ring
      _ ≤ (1 + m) * (2 * g) := Nat.mul_le_mul_left _ m1
      _ = (2 + 2 * m) * g := by ring
      _ ≤ g * g := Nat.mul_le_mul_right _ (by omega)
      _ = g ^ 2 := by ring
  have a3 : (g * B + g ^ 2 * lam) * (m + m * m) * K ≤ g ^ 3 * B + g ^ 4 * lam := by
    calc (g * B + g ^ 2 * lam) * (m + m * m) * K = (g * B + g ^ 2 * lam) * ((m + m * m) * K) := by ring
      _ ≤ (g * B + g ^ 2 * lam) * g ^ 2 := Nat.mul_le_mul_left _ a2
      _ = g ^ 3 * B + g ^ 4 * lam := by ring
  unfold bNext
  rw [← hm]
  omega
end PaddedDescent.F.Arith
