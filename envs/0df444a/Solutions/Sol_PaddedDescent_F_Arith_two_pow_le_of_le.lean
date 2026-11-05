-- Prove2me | solution 1 for PaddedDescent.F.Arith.two_pow_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:04:15.449383+00:00
-- url     : https://prove2.me/submissions/0fd0e15c-601c-45f4-a5c7-2367eef77859

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {k Δ s n F : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution {e : ℕ} (hF : 2 ^ (8 * Xof s n) ≤ F) (he : e ≤ 8 * Xof s n) : 2 ^ e ≤ F :=
  le_trans (Nat.pow_le_pow_right (by norm_num) he) hF
end PaddedDescent.F.Arith
