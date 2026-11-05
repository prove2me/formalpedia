-- Prove2me | solution 1 for PaddedDescent.F.Arith.inv_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:24.519354+00:00
-- url     : https://prove2.me/submissions/22940eaa-2fe3-4b26-95bc-1809d899b168

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Definitions.Def_PaddedDescent_F_ArithTop
import Theorems.Thm_PaddedDescent_F_Arith_four_sq_mul_lamG_le
import Theorems.Thm_PaddedDescent_F_Arith_inv_top_aux

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
variable {K g Ub P X : ℕ}
namespace PaddedDescent.F.Arith
theorem _root_.solution {t Z u r n s : ℕ} (hK : 0 < K) (hP : 4 * (g * P) ≤ K * X) (hU : Ub ≤ u * n + r) (hn : n ≤ 2 ^ s * X)
    (ht : 8963 ^ t * (2 * u * 2 ^ s) ≤ 10000 ^ t) (hZ : K ^ 2 + r ≤ Z) :
    8963 ^ t * (K ^ 2 * lamG K g Ub P) ≤ 10000 ^ t * X + 8963 ^ t * Z := by
  have h1 := four_sq_mul_lamG_le (Ub := Ub) hK hP
  have hab : 8963 ^ t ≤ 10000 ^ t := Nat.pow_le_pow_left (by norm_num) t
  have h2 : u * n ≤ u * 2 ^ s * X := by
    calc u * n ≤ u * (2 ^ s * X) := Nat.mul_le_mul_left _ hn
      _ = u * 2 ^ s * X := by ring
  have h3 : 8963 ^ t * (2 * (u * 2 ^ s * X)) ≤ 10000 ^ t * X := by
    calc 8963 ^ t * (2 * (u * 2 ^ s * X)) = 8963 ^ t * (2 * u * 2 ^ s) * X := by ring
      _ ≤ 10000 ^ t * X := Nat.mul_le_mul_right _ ht
  have h4 : 8963 ^ t * X ≤ 10000 ^ t * X := Nat.mul_le_mul_right _ hab
  have h5 : 4 * (K ^ 2 * lamG K g Ub P) ≤ 4 * Z + 4 * (u * 2 ^ s * X) + X := by omega
  exact inv_top_aux h3 h4 h5
end PaddedDescent.F.Arith
