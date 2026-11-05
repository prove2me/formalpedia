-- Prove2me | solution 1 for PaddedDescent.F.Arith.mul_Ubar_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:57:28.617038+00:00
-- url     : https://prove2.me/submissions/e7d78d20-a156-4997-adbb-61fc1b9a6dcc

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
theorem _root_.solution (g lam : ℕ) :
    800 * Ubar g lam ≤ 800 * (g ^ 3 * lam) + 717 * (g ^ 4 * lam) + 400 * g ^ 4 + 800 := by
  have h1 : g ^ 2 * (g - 1) * lam ≤ g ^ 3 * lam := by
    refine Nat.mul_le_mul_right _ ?_
    calc g ^ 2 * (g - 1) ≤ g ^ 2 * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = g ^ 3 := by ring
  have h2 : 800 * (717 * g ^ 4 * lam / 800) ≤ 717 * g ^ 4 * lam := Nat.mul_div_le _ _
  have h3 : 2 * (g ^ 4 / 2) ≤ g ^ 4 := Nat.mul_div_le _ _
  have h4 : 717 * g ^ 4 * lam = 717 * (g ^ 4 * lam) := by ring
  unfold Ubar
  omega
end PaddedDescent.F.Arith
