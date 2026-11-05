-- Prove2me | solution 1 for PaddedDescent.F.Arith.Inv.succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:48.098786+00:00
-- url     : https://prove2.me/submissions/dd802a0a-001b-463b-ba24-d97a73dd8761

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
import Theorems.Thm_PaddedDescent_F_Arith_Kseq_succ_sq
import Theorems.Thm_PaddedDescent_F_Arith_pow_succ_le_mul_Kseq
import Theorems.Thm_PaddedDescent_Kseq_pos


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}
namespace PaddedDescent.F.Arith
namespace Inv
theorem _root_.solution (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) : gseq j ^ 4 * lam ≤ Kseq j * (X + Z) := by
  have h1 := h.geo
  rw [Kseq_succ_sq] at h1
  have h2 := pow_succ_le_mul_Kseq j
  have hK : 0 < Kseq j := Kseq_pos j
  have hp : 0 < 8963 ^ (j + 1) := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hp
  calc 8963 ^ (j + 1) * (gseq j ^ 4 * lam) ≤ 10000 ^ (j + 1) * X + 8963 ^ (j + 1) * Z := h1
    _ ≤ 8963 ^ (j + 1) * Kseq j * X + 8963 ^ (j + 1) * Kseq j * Z :=
        Nat.add_le_add (Nat.mul_le_mul_right _ h2) (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hK))
    _ = 8963 ^ (j + 1) * (Kseq j * (X + Z)) := by ring
end Inv
end PaddedDescent.F.Arith
