-- Prove2me | solution 1 for Sendov.B22_24.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:05.963298+00:00
-- url     : https://prove2.me/submissions/a91403e2-6478-4aa8-a447-1d6b6e94dcdd

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
import Theorems.Thm_Sendov_B22_24_M_lo
import Theorems.Thm_Sendov_B22_24_M_hi
import Theorems.Thm_Sendov_B22_24_A_hi
import Theorems.Thm_Sendov_B22_24_c_lo_nonneg
import Theorems.Thm_Sendov_B22_24_integral_lo
import Theorems.Thm_Sendov_B22_24_P_pos
import Theorems.Thm_Sendov_R_le_batch
import Theorems.Thm_Sendov_alpha_le_half_M
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_l1_cons
import Theorems.Thm_Sendov_l1_nil
import Theorems.Thm_Sendov_l1row_cons
import Theorems.Thm_Sendov_l1row_nil
import Theorems.Thm_Sendov_npev_cons
import Theorems.Thm_Sendov_npev_nil
import Theorems.Thm_Sendov_pevZ_cons
import Theorems.Thm_Sendov_pevZ_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_qrow_length
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rowZ_cons
import Theorems.Thm_Sendov_rowZ_length
import Theorems.Thm_Sendov_rowZ_nil
import Theorems.Thm_Sendov_rscale_length
import Theorems.Thm_Sendov_three_add_pos
import Theorems.Thm_Sendov_unpackN_succ
import Theorems.Thm_Sendov_unpackN_zero
import Theorems.Thm_Sendov_unpackZ_succ
import Theorems.Thm_Sendov_unpackZ_zero
import Theorems.Thm_Sendov_wsumZ_cons
import Theorems.Thm_Sendov_wsumZ_nil
import Theorems.Thm_Sendov_wsum_cons
import Theorems.Thm_Sendov_wsum_nil
attribute [local simp] Sendov.gg0_length
attribute [local simp] Sendov.gg1_length
attribute [local simp] Sendov.gg2_length
attribute [local simp] Sendov.l1_cons
attribute [local simp] Sendov.l1_nil
attribute [local simp] Sendov.l1row_cons
attribute [local simp] Sendov.l1row_nil
attribute [local simp] Sendov.npev_cons
attribute [local simp] Sendov.npev_nil
attribute [local simp] Sendov.pevZ_cons
attribute [local simp] Sendov.pevZ_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.qrow_length
attribute [local simp] Sendov.rev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rowZ_cons
attribute [local simp] Sendov.rowZ_length
attribute [local simp] Sendov.rowZ_nil
attribute [local simp] Sendov.rscale_length
attribute [local simp] Sendov.unpackN_succ
attribute [local simp] Sendov.unpackN_zero
attribute [local simp] Sendov.unpackZ_succ
attribute [local simp] Sendov.unpackZ_zero
attribute [local simp] Sendov.wsumZ_cons
attribute [local simp] Sendov.wsumZ_nil
attribute [local simp] Sendov.wsum_cons
attribute [local simp] Sendov.wsum_nil



set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
set_option maxHeartbeats 2000000
namespace Sendov.B22_24
theorem _root_.solution {n : ℕ} (h0 : 22 ≤ n) (h1 : n ≤ 24) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 23 / 2 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (24 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (24 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 22) (n := n) (n₁ := 24) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((22 : ℕ) : ℝ) - 4 = 18 by norm_num] at hb
  rw [show (18 : ℝ) / 2 = ((9 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 21) + 1 / (4 * 21 * (3 + α))
      + (1 - 2 * α / 23) ^ 2 * 24 * 23 * (24 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 21 * (3 + α)) ^ 9))
      = 1 - (72676691260477709153931 + 243335498910644300539743 * α + 365647629606098581621152 * α ^ 2 + 324203560761134112575706 * α ^ 3 + 187220150267586036026391 * α ^ 4 + 72995868351568741088853 * α ^ 5 + 18997181712653091143742 * α ^ 6 + 2912276075526675669294 * α ^ 7 - 47524187765551795452 * α ^ 8 - 572344038827543054862 * α ^ 9 + 60958599043408078986 * α ^ 10 + 1608150216459380292 * α ^ 11 + 37160884428953616 * α ^ 12 - 4770728942909184 * α ^ 13 - 508194774105984 * α ^ 14 - 24843494479104 * α ^ 15 - 745526594304 * α ^ 16 - 14490071808 * α ^ 17 - 179034112 * α ^ 18 - 1285120 * α ^ 19 - 4096 * α ^ 20) / (1789880961368575530 * (3 + α) ^ 10) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (72676691260477709153931 + 243335498910644300539743 * α + 365647629606098581621152 * α ^ 2 + 324203560761134112575706 * α ^ 3 + 187220150267586036026391 * α ^ 4 + 72995868351568741088853 * α ^ 5 + 18997181712653091143742 * α ^ 6 + 2912276075526675669294 * α ^ 7 - 47524187765551795452 * α ^ 8 - 572344038827543054862 * α ^ 9 + 60958599043408078986 * α ^ 10 + 1608150216459380292 * α ^ 11 + 37160884428953616 * α ^ 12 - 4770728942909184 * α ^ 13 - 508194774105984 * α ^ 14 - 24843494479104 * α ^ 15 - 745526594304 * α ^ 16 - 14490071808 * α ^ 17 - 179034112 * α ^ 18 - 1285120 * α ^ 19 - 4096 * α ^ 20) / (1789880961368575530 * (3 + α) ^ 10) := div_pos hP (by positivity)
  linarith
end Sendov.B22_24
