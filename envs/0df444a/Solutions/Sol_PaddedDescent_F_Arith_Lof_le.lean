-- Prove2me | solution 1 for PaddedDescent.F.Arith.Lof_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:04:50.947992+00:00
-- url     : https://prove2.me/submissions/baef8f32-5057-48d4-a454-2bedfc4a9cfb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_ArithGlob
import Definitions.Def_PaddedDescent_F_ArithTop
import Definitions.Def_PaddedDescent_F_ArithWalk
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Theorems.Thm_PaddedDescent_lin_lt_Ytop
import Theorems.Thm_PaddedDescent_size_le_sqrt


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F.Arith
theorem _root_.solution (s n : ℕ) : Lof s n ≤ 2 * Ytop s * (Nat.sqrt n + 1) := by
  have h1 := size_le_sqrt n
  have h2 := lin_lt_Ytop s
  have h3 : 2 * (Nat.sqrt n + 1) ≤ Ytop s * (Nat.sqrt n + 1) := Nat.mul_le_mul_right _ (by omega)
  have h4 : Ytop s ≤ Ytop s * (Nat.sqrt n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have e : 2 * Ytop s * (Nat.sqrt n + 1) = 2 * (Ytop s * (Nat.sqrt n + 1)) := by ring
  rw [e]
  unfold Lof
  omega
end PaddedDescent.F.Arith
