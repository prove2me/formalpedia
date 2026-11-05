-- Prove2me | solution 1 for PaddedDescent.F.Arith.coeff_le_Ktop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:02:57.352748+00:00
-- url     : https://prove2.me/submissions/81585ef5-7721-4552-98e8-c024e5647470

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_coeff_le
import Theorems.Thm_PaddedDescent_Ktop_lower


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s : ℕ) : 4 * (s + 8) ^ 6 * 2 ^ s ≤ Ktop s := by
  calc 4 * (s + 8) ^ 6 * 2 ^ s ≤ 2 ^ (6 * s + 20) * 2 ^ s := Nat.mul_le_mul_right _ (coeff_le s)
    _ = 2 ^ (6 * s + 20 + s) := by rw [← pow_add]
    _ ≤ 2 ^ (52 * s + 692) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ Ktop s := Ktop_lower s
end PaddedDescent.F.Arith
