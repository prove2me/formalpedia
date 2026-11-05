-- Prove2me | solution 1 for PaddedDescent.mul_Ktop_pow_le_Ytop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:21:02.200005+00:00
-- url     : https://prove2.me/submissions/d800290d-ea5a-46c3-8373-a6a3b001fcba

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_Seq
import Theorems.Thm_PaddedDescent_Ytop_eq
import Theorems.Thm_PaddedDescent_Ktop_lower
import Theorems.Thm_PaddedDescent_Ktop_pos

set_option autoImplicit false
section
section
open PaddedDescent
namespace PaddedDescent
theorem _root_.solution {C e : ℕ} (hC : C ≤ 2 ^ 500) (he : e ≤ 15) (s : ℕ) : C * Ktop s ^ e ≤ Ytop s := by
  have h1 : 2 ^ 500 ≤ Ktop s := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Ktop_lower s)
  calc C * Ktop s ^ e ≤ Ktop s * Ktop s ^ 15 :=
        Nat.mul_le_mul (hC.trans h1) (Nat.pow_le_pow_right (Ktop_pos s) he)
    _ = Ktop s ^ 16 := by ring
    _ ≤ 9 * Ktop s ^ 16 := Nat.le_mul_of_pos_left _ (by norm_num)
    _ = Ytop s := (Ytop_eq s).symm
end PaddedDescent
