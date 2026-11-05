-- Prove2me | solution 1 for PaddedDescent.F.Arith.Ktop_le_gtop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:50:14.161828+00:00
-- url     : https://prove2.me/submissions/6e741d94-0f82-479d-a33e-6199cbd83b6e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_gtop_eq


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : Ktop s ≤ gtop s := by
  have h : Ktop s ≤ Ktop s ^ 8 := Nat.le_self_pow (by norm_num) _
  rw [gtop_eq]; omega
end PaddedDescent.F.Arith
