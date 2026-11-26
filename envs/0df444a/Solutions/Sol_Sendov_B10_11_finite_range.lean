-- Prove2me | solution 1 for Sendov.B10_11.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:09:57.400191+00:00
-- url     : https://prove2.me/submissions/10225187-0b4c-43f4-a1e8-c2676205f0d4

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11
import Theorems.Thm_Sendov_B10_11_M_lo
import Theorems.Thm_Sendov_B10_11_M_hi
import Theorems.Thm_Sendov_B10_11_A_hi
import Theorems.Thm_Sendov_B10_11_c_lo_nonneg
import Theorems.Thm_Sendov_B10_11_integral_lo
import Theorems.Thm_Sendov_B10_11_P_pos
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
open Sendov.B10_11
set_option maxHeartbeats 2000000
namespace Sendov.B10_11
theorem _root_.solution {n : ℕ} (h0 : 10 ≤ n) (h1 : n ≤ 11) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 5 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (11 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (11 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 10) (n := n) (n₁ := 11) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((10 : ℕ) : ℝ) - 4 = 6 by norm_num] at hb
  rw [show (6 : ℝ) / 2 = ((3 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 9) + 1 / (4 * 9 * (3 + α))
      + (1 - 2 * α / 10) ^ 2 * 11 * 10 * (11 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 9 * (3 + α)) ^ 3))
      = 1 - (32349375 + 39180105 * α + 10086687 * α ^ 2 - 24445935 * α ^ 3 + 11871036 * α ^ 4 - 351846 * α ^ 5 - 81598 * α ^ 6 - 4664 * α ^ 7 - 88 * α ^ 8) / (680400 * (3 + α) ^ 4) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (32349375 + 39180105 * α + 10086687 * α ^ 2 - 24445935 * α ^ 3 + 11871036 * α ^ 4 - 351846 * α ^ 5 - 81598 * α ^ 6 - 4664 * α ^ 7 - 88 * α ^ 8) / (680400 * (3 + α) ^ 4) := div_pos hP (by positivity)
  linarith
end Sendov.B10_11
