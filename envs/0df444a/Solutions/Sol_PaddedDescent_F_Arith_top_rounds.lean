-- Prove2me | solution 1 for PaddedDescent.F.Arith.top_rounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:05:54.958595+00:00
-- url     : https://prove2.me/submissions/427a32f6-ced5-42d6-a363-ff57929d823c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_F_Arith_two_pow_le_of_le
import Theorems.Thm_PaddedDescent_F_Arith_sum_choose_le_two_pow


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {k Δ s n F : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution (hs : s0K k ≤ s) (hF : 2 ^ (8 * Xof s n) ≤ F) :
    2 * (∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j) ≤ F + 1 := by
  have h1 : ∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j ≤ 2 ^ Xof s n :=
    sum_choose_le_two_pow hs n
  have h0 : 1 ≤ Xof s n := Nat.le_add_left 1 _
  have h2 : 2 ^ (Xof s n + 1) ≤ F := two_pow_le_of_le hF (by omega)
  rw [pow_succ] at h2
  omega
end PaddedDescent.F.Arith
