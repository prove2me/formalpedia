-- Prove2me | solution 1 for PaddedDescent.F.Arith.Inv.step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:12:23.294777+00:00
-- url     : https://prove2.me/submissions/c97dedb2-4d10-4087-95ec-a1400a2a305a

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
import Theorems.Thm_PaddedDescent_F_Arith_Kseq_succ_cube
import Theorems.Thm_PaddedDescent_F_Arith_Kseq_mono
import Theorems.Thm_PaddedDescent_F_Arith_geo_step
import Theorems.Thm_PaddedDescent_F_Arith_bits_step
import Theorems.Thm_PaddedDescent_F_Arith_count_step
import Theorems.Thm_P2M_PaddedDescent_F_Arith_bNext_le__179d733ec018
import Theorems.Thm_PaddedDescent_F_Arith_lamNext_contract
import Theorems.Thm_PaddedDescent_F_Arith_nRect_le
import Theorems.Thm_PaddedDescent_F_Arith_pow_facts
import Theorems.Thm_PaddedDescent_F_Arith_six_cube_mul_cube_le
import Theorems.Thm_PaddedDescent_Kseq_ge
import Theorems.Thm_PaddedDescent_Kseq_le_gseq
import Theorems.Thm_PaddedDescent_two_pow_mul_Kseq_le_gseq


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Arith
open Groundwork.Prog (nRect)
variable {t X Z Qm Wm L j lam B cnt : ℕ}
namespace PaddedDescent.F.Arith
namespace Inv
theorem _root_.solution (hZ : 25 * Kseq t ^ 2 ≤ 2 * Z) (hZQ : Z ≤ Qm) (hL : Qm + 1 ≤ 2 ^ L) (hj : j + 1 ≤ t)
    (h : Inv t X Z Qm Wm L (j + 1) lam B cnt) :
    Inv t X Z Qm Wm L j (lamNext (Kseq j) (gseq j) lam) (bNext (Kseq j) (gseq j) lam B)
      (cnt * (lam + 1) ^ nRect (gseq j)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Kseq_succ_sq] at h1 h2 h4
  rw [Kseq_succ_cube] at h3
  have hK : 256 ≤ Kseq j := Kseq_ge j
  have hKg : Kseq j ≤ gseq j := Kseq_le_gseq j
  have h47 := two_pow_mul_Kseq_le_gseq j
  have hg2 : 2 * Kseq j ≤ gseq j := le_trans (Nat.mul_le_mul_right _ (by norm_num)) h47
  have hg20 : 2 ^ 20 ≤ gseq j :=
    le_trans (by norm_num : 2 ^ 20 ≤ 2 ^ 47 * 1) (le_trans (Nat.mul_le_mul_left _ (by omega : 1 ≤ Kseq j)) h47)
  have hG : gseq j ^ 4 ≤ Kseq t ^ 2 := by
    rw [← Kseq_succ_sq]; exact Nat.pow_le_pow_left (Kseq_mono hj) 2
  have O1 := lamNext_contract hKg hg20 lam
  have O2 := bNext_le' hK hKg lam B
  have O8a := six_cube_mul_cube_le hg2
  obtain ⟨O8b, O8c⟩ := pow_facts hg2
  have e4 : (gseq j * gseq j) ^ 2 = gseq j ^ 4 := by ring
  rw [e4] at O8c
  have hG1 : 1 ≤ gseq j ^ 4 := Nat.one_le_pow _ _ (by omega)
  have c1 : lam + 1 ≤ 2 ^ L := by
    have : lam ≤ gseq j ^ 4 * lam := Nat.le_mul_of_pos_left _ hG1
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_succ, pow_succ] at h1
    exact geo_step O1 (by omega) h1
  · omega
  · exact bits_step O2 O8a O8b h2 h3
  · exact count_step c1 (nRect_le _) O8c h4
end Inv
end PaddedDescent.F.Arith
