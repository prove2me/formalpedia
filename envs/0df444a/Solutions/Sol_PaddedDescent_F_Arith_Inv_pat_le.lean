-- Prove2me | solution 1 for PaddedDescent.F.Arith.Inv.pat_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:10:26.528949+00:00
-- url     : https://prove2.me/submissions/19b5513f-b508-4839-ae1e-2d56a9866cd4

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
import Theorems.Thm_PaddedDescent_F_Arith_Kseq_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_Arith_nRect_le
import Theorems.Thm_PaddedDescent_Kseq_pos


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}
namespace PaddedDescent.F.Arith
namespace Inv
theorem _root_.solution (hL : Qm + 1 ≤ 2 ^ L) (hj : j + 1 ≤ t) (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) :
    (lam + 1) ^ nRect (gseq j) ≤ 2 ^ (L * Kseq t ^ 2) := by
  have h2 := h.crude
  have hK1 : 1 ≤ Kseq (j + 1) ^ 2 := Nat.one_le_pow _ _ (Kseq_pos _)
  have c1 : lam + 1 ≤ 2 ^ L := by
    have : lam ≤ Kseq (j + 1) ^ 2 * lam := Nat.le_mul_of_pos_left _ hK1
    omega
  have hG : gseq j ^ 4 ≤ Kseq t ^ 2 := by
    rw [← Kseq_succ_sq]; exact Nat.pow_le_pow_left (Kseq_mono hj) 2
  calc (lam + 1) ^ nRect (gseq j) ≤ (2 ^ L) ^ nRect (gseq j) := Nat.pow_le_pow_left c1 _
    _ ≤ (2 ^ L) ^ (Kseq t ^ 2) :=
        Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by norm_num)) ((nRect_le _).trans hG)
    _ = 2 ^ (L * Kseq t ^ 2) := by rw [← pow_mul]
end Inv
end PaddedDescent.F.Arith
