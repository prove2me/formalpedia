-- Prove2me | solution 1 for Sendov.B16_18.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:10:27.087155+00:00
-- url     : https://prove2.me/submissions/fceed21b-463c-4234-b810-4c734759f11f

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
import Theorems.Thm_Sendov_B16_18_M_lo
import Theorems.Thm_Sendov_B16_18_M_hi
import Theorems.Thm_Sendov_B16_18_A_hi
import Theorems.Thm_Sendov_B16_18_c_lo_nonneg
import Theorems.Thm_Sendov_B16_18_integral_lo
import Theorems.Thm_Sendov_B16_18_P_pos
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
open Sendov.B16_18
set_option maxHeartbeats 2000000
namespace Sendov.B16_18
theorem _root_.solution {n : ℕ} (h0 : 16 ≤ n) (h1 : n ≤ 18) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 17 / 2 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (18 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (18 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 16) (n := n) (n₁ := 18) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((16 : ℕ) : ℝ) - 4 = 12 by norm_num] at hb
  rw [show (12 : ℝ) / 2 = ((6 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 15) + 1 / (4 * 15 * (3 + α))
      + (1 - 2 * α / 17) ^ 2 * 18 * 17 * (18 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 15 * (3 + α)) ^ 6))
      = 1 - (308547940078125 + 716274580556250 * α + 701075142421875 * α ^ 2 + 366034929547500 * α ^ 3 + 98713082723625 * α ^ 4 - 785317395690 * α ^ 5 - 34202916258669 * α ^ 6 + 6366700041480 * α ^ 7 + 121732471512 * α ^ 8 - 9494954208 * α ^ 9 - 1551607200 * α ^ 10 - 87661568 * α ^ 11 - 2586240 * α ^ 12 - 39936 * α ^ 13 - 256 * α ^ 14) / (215371406250 * (3 + α) ^ 7) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (308547940078125 + 716274580556250 * α + 701075142421875 * α ^ 2 + 366034929547500 * α ^ 3 + 98713082723625 * α ^ 4 - 785317395690 * α ^ 5 - 34202916258669 * α ^ 6 + 6366700041480 * α ^ 7 + 121732471512 * α ^ 8 - 9494954208 * α ^ 9 - 1551607200 * α ^ 10 - 87661568 * α ^ 11 - 2586240 * α ^ 12 - 39936 * α ^ 13 - 256 * α ^ 14) / (215371406250 * (3 + α) ^ 7) := div_pos hP (by positivity)
  linarith
end Sendov.B16_18
