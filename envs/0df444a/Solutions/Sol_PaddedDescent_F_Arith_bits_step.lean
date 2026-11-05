-- Prove2me | solution 1 for PaddedDescent.F.Arith.bits_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:32.266973+00:00
-- url     : https://prove2.me/submissions/84375c5b-4b61-47ca-9597-94279868b575

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution {B B' K3 G6 G3 q Qm Wm : ℕ} (O2 : B' ≤ 6 * (G3 * B) + 8 * q) (O8a : 6 * G3 * K3 ≤ G6)
    (O8b : 24 * K3 ≤ 16 * G6) (hq : q ≤ Qm) (h3 : B * G6 + 16 * Qm * G6 ≤ Wm) :
    B' * K3 + 16 * Qm * K3 ≤ Wm := by
  have b1 : B' * K3 ≤ (6 * (G3 * B) + 8 * q) * K3 := Nat.mul_le_mul_right _ O2
  have b2 : 6 * G3 * K3 * B ≤ G6 * B := Nat.mul_le_mul_right _ O8a
  have b3 : 8 * q * K3 ≤ 8 * Qm * K3 := Nat.mul_le_mul_right _ (by omega)
  have b4 : Qm * (24 * K3) ≤ Qm * (16 * G6) := Nat.mul_le_mul_left _ O8b
  nlinarith
end PaddedDescent.F.Arith
