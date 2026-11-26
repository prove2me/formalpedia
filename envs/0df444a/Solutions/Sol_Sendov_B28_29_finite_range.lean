-- Prove2me | solution 1 for Sendov.B28_29.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:34.758961+00:00
-- url     : https://prove2.me/submissions/60ae897e-b416-4a7b-bb78-2639ad7b5bb0

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29
import Theorems.Thm_Sendov_B28_29_M_lo
import Theorems.Thm_Sendov_B28_29_M_hi
import Theorems.Thm_Sendov_B28_29_A_hi
import Theorems.Thm_Sendov_B28_29_c_lo_nonneg
import Theorems.Thm_Sendov_B28_29_integral_lo
import Theorems.Thm_Sendov_B28_29_P_pos
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
open Sendov.B28_29
set_option maxHeartbeats 2000000
namespace Sendov.B28_29
theorem _root_.solution {n : ℕ} (h0 : 28 ≤ n) (h1 : n ≤ 29) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 14 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (29 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (29 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 28) (n := n) (n₁ := 29) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((28 : ℕ) : ℝ) - 4 = 24 by norm_num] at hb
  rw [show (24 : ℝ) / 2 = ((12 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 27) + 1 / (4 * 27 * (3 + α))
      + (1 - 2 * α / 28) ^ 2 * 29 * 28 * (29 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 27 * (3 + α)) ^ 12))
      = 1 - (426450318135882438427115499581616 + 1858834576882378710373815569972592 * α + 3736799374885893548337894566091516 * α ^ 2 + 4586209917810757974592827719731488 * α ^ 3 + 3832530771213891318426391118558376 * α ^ 4 + 2301315780911216714788724083158840 * α ^ 5 + 1020320104787175718704940125987654 * α ^ 6 + 337351267574328588560584527446352 * α ^ 7 + 82684042360278469454015755593696 * α ^ 8 + 14571761439373687941870063150072 * α ^ 9 + 1651893249078514632421437650658 * α ^ 10 + 16915365961758038105007429024 * α ^ 11 - 175858786927760049854457800868 * α ^ 12 + 13481653528168191298544554836 * α ^ 13 + 281552860237833486968732937 * α ^ 14 + 14047072236623243173813992 * α ^ 15 - 9139934377157415820848 * α ^ 16 - 45943869853012600689984 * α ^ 17 - 3291728447735177292432 * α ^ 18 - 135117714229500881664 * α ^ 19 - 3776901841060823808 * α ^ 20 - 75424649382531072 * α ^ 21 - 1084454315870976 * α ^ 22 - 11022972807168 * α ^ 23 - 75437817856 * α ^ 24 - 312639488 * α ^ 25 - 593920 * α ^ 26) / (378820688032445824710417600 * (3 + α) ^ 13) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (426450318135882438427115499581616 + 1858834576882378710373815569972592 * α + 3736799374885893548337894566091516 * α ^ 2 + 4586209917810757974592827719731488 * α ^ 3 + 3832530771213891318426391118558376 * α ^ 4 + 2301315780911216714788724083158840 * α ^ 5 + 1020320104787175718704940125987654 * α ^ 6 + 337351267574328588560584527446352 * α ^ 7 + 82684042360278469454015755593696 * α ^ 8 + 14571761439373687941870063150072 * α ^ 9 + 1651893249078514632421437650658 * α ^ 10 + 16915365961758038105007429024 * α ^ 11 - 175858786927760049854457800868 * α ^ 12 + 13481653528168191298544554836 * α ^ 13 + 281552860237833486968732937 * α ^ 14 + 14047072236623243173813992 * α ^ 15 - 9139934377157415820848 * α ^ 16 - 45943869853012600689984 * α ^ 17 - 3291728447735177292432 * α ^ 18 - 135117714229500881664 * α ^ 19 - 3776901841060823808 * α ^ 20 - 75424649382531072 * α ^ 21 - 1084454315870976 * α ^ 22 - 11022972807168 * α ^ 23 - 75437817856 * α ^ 24 - 312639488 * α ^ 25 - 593920 * α ^ 26) / (378820688032445824710417600 * (3 + α) ^ 13) := div_pos hP (by positivity)
  linarith
end Sendov.B28_29
