-- Prove2me | solution 1 for Sendov.B14_15.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:10:23.458536+00:00
-- url     : https://prove2.me/submissions/41ca7d93-90a4-40e8-98db-4000a97d40d4

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15
import Theorems.Thm_Sendov_B14_15_M_lo
import Theorems.Thm_Sendov_B14_15_M_hi
import Theorems.Thm_Sendov_B14_15_A_hi
import Theorems.Thm_Sendov_B14_15_c_lo_nonneg
import Theorems.Thm_Sendov_B14_15_integral_lo
import Theorems.Thm_Sendov_B14_15_P_pos
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
open Sendov.B14_15
set_option maxHeartbeats 2000000
namespace Sendov.B14_15
theorem _root_.solution {n : ℕ} (h0 : 14 ≤ n) (h1 : n ≤ 15) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 7 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (15 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (15 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 14) (n := n) (n₁ := 15) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((14 : ℕ) : ℝ) - 4 = 10 by norm_num] at hb
  rw [show (10 : ℝ) / 2 = ((5 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 13) + 1 / (4 * 13 * (3 + α))
      + (1 - 2 * α / 14) ^ 2 * 15 * 14 * (15 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 13 * (3 + α)) ^ 5))
      = 1 - (4540012290450 + 9000770719122 * α + 7217967952260 * α ^ 2 + 2789503991820 * α ^ 3 + 226924812075 * α ^ 4 - 867448623285 * α ^ 5 + 235182487819 * α ^ 6 + 1315276135 * α ^ 7 - 765536900 * α ^ 8 - 78585080 * α ^ 9 - 3463520 * α ^ 10 - 74480 * α ^ 11 - 640 * α ^ 12) / (9606092496 * (3 + α) ^ 6) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (4540012290450 + 9000770719122 * α + 7217967952260 * α ^ 2 + 2789503991820 * α ^ 3 + 226924812075 * α ^ 4 - 867448623285 * α ^ 5 + 235182487819 * α ^ 6 + 1315276135 * α ^ 7 - 765536900 * α ^ 8 - 78585080 * α ^ 9 - 3463520 * α ^ 10 - 74480 * α ^ 11 - 640 * α ^ 12) / (9606092496 * (3 + α) ^ 6) := div_pos hP (by positivity)
  linarith
end Sendov.B14_15
