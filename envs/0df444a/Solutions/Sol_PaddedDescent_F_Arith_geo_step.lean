-- Prove2me | solution 1 for PaddedDescent.F.Arith.geo_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:07.121347+00:00
-- url     : https://prove2.me/submissions/50ea144b-9c4f-41c9-9f85-d822826e4ab8

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
theorem _root_.solution {a b q' q G X Z : ℕ} (O1 : 10000 * q' ≤ 8963 * q + 10000 * G) (hG : 10000 * G ≤ 1037 * Z)
    (h1 : a * 8963 * q ≤ b * 10000 * X + a * 8963 * Z) : a * q' ≤ b * X + a * Z := by
  have a1 := Nat.mul_le_mul_left a O1
  have a2 := Nat.mul_le_mul_left a hG
  nlinarith
end PaddedDescent.F.Arith
