-- Prove2me | solution 1 for PaddedDescent.F.Arith.Inv.work_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:16:29.197494+00:00
-- url     : https://prove2.me/submissions/f712d35e-38d6-44b8-bb67-8fd7a97a2df4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Seq
import Definitions.Def_PaddedDescent_F_ArithLevel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_PaddedDescent_F_ArithInv
import Theorems.Thm_PaddedDescent_F_Arith_Kseq_mono
import Theorems.Thm_PaddedDescent_F_Arith_Inv_mul_le
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Arith_instLen_le
import Theorems.Thm_PaddedDescent_Kseq_pos
attribute [local fun_prop] Groundwork.PolyT.count



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}
namespace PaddedDescent.F.Arith
namespace Inv
theorem _root_.solution {Lw : ℕ} (hLw : Kseq t * (3 * Wm + 14) + 4 * Qm + 10 ≤ 2 ^ Lw) (hj : j ≤ t)
    (h : Inv t X Z Qm Wm L j lam B cnt) :
    cnt * instLen (Kseq j) lam B + 2 ≤ 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw + 1) := by
  have hK1 : 1 ≤ Kseq j ^ 2 := Nat.one_le_pow _ _ (Kseq_pos _)
  have w1 : cnt ≤ 2 ^ (L * (2 * Kseq t ^ 2)) :=
    le_trans (Nat.le_mul_of_pos_right _ (by positivity)) h.count
  have w2 : (Kseq j - 1) * lam ≤ X + Z := le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) h.mul_le
  have w3 : B ≤ Wm := by
    have : B ≤ B * Kseq j ^ 3 := Nat.le_mul_of_pos_right _ (Nat.pow_pos (Kseq_pos _))
    have := h.bits
    omega
  have w4 : lam ≤ Qm := le_trans (Nat.le_mul_of_pos_left _ hK1) h.crude
  have w5 : Kseq j * (3 * B + 14) + 4 * lam + 10 ≤ 2 ^ Lw := by
    have : Kseq j * (3 * B + 14) ≤ Kseq t * (3 * Wm + 14) := Nat.mul_le_mul (Kseq_mono hj) (by omega)
    omega
  have w6 : cnt * instLen (Kseq j) lam B ≤ 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw) := by
    calc cnt * instLen (Kseq j) lam B
        ≤ 2 ^ (L * (2 * Kseq t ^ 2)) * (2 ^ (X + Z) * 2 ^ Lw) :=
          Nat.mul_le_mul w1 ((instLen_le _ _ _).trans
            (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) w2) w5))
      _ = 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw) := by rw [pow_add, pow_add]; ring
  have w7 : 2 ≤ 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw) := by
    have : 2 ^ 1 ≤ 2 ^ Lw := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      by_contra hc
      have : Lw = 0 := by omega
      subst this
      omega
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ Lw := this
      _ ≤ 2 ^ (L * (2 * Kseq t ^ 2) + (X + Z) + Lw) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega
end Inv
end PaddedDescent.F.Arith
