-- Prove2me | solution 1 for PaddedDescent.F.Arith.pow_le_two_pow_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:40.636057+00:00
-- url     : https://prove2.me/submissions/eb94591a-d873-4ca1-a4b2-796677d9eb49

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
import Theorems.Thm_PaddedDescent_F_Arith_pow_le_two_pow_mul

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution {K g : ℕ} (hg : K ≤ g) : K ^ g ≤ 2 ^ (g * g) :=
  le_trans (pow_le_two_pow_mul K g) (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hg))
end PaddedDescent.F.Arith
