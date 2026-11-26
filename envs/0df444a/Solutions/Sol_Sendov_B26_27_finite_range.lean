-- Prove2me | solution 1 for Sendov.B26_27.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:18.217961+00:00
-- url     : https://prove2.me/submissions/d0fb8dbc-e240-4ad6-8dfd-f5fac6902285

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27
import Theorems.Thm_Sendov_B26_27_M_lo
import Theorems.Thm_Sendov_B26_27_M_hi
import Theorems.Thm_Sendov_B26_27_A_hi
import Theorems.Thm_Sendov_B26_27_c_lo_nonneg
import Theorems.Thm_Sendov_B26_27_integral_lo
import Theorems.Thm_Sendov_B26_27_P_pos
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
open Sendov.B26_27
set_option maxHeartbeats 2000000
namespace Sendov.B26_27
theorem _root_.solution {n : ℕ} (h0 : 26 ≤ n) (h1 : n ≤ 27) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 13 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (27 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (27 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 26) (n := n) (n₁ := 27) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((26 : ℕ) : ℝ) - 4 = 22 by norm_num] at hb
  rw [show (22 : ℝ) / 2 = ((11 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 25) + 1 / (4 * 25 * (3 + α))
      + (1 - 2 * α / 26) ^ 2 * 27 * 26 * (27 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 25 * (3 + α)) ^ 11))
      = 1 - (750669183453805732727050781250 + 3020533706655215263366699218750 * α + 5564839729610338783264160156250 * α ^ 2 + 6204652935907732786560058593750 * α ^ 3 + 4659850847351595430480957031250 * α ^ 4 + 2480313988118708551463378906250 * α ^ 5 + 956953438533800725637460937500 * α ^ 6 + 267988469385291406396875000000 * α ^ 7 + 53061280626889862612388984375 * α ^ 8 + 6649776660279075672227540625 * α ^ 9 + 67029306131497703210255025 * α ^ 10 - 797547671168471728584421521 * α ^ 11 + 69793209950586805764791132 * α ^ 12 + 1582701213221515173844854 * α ^ 13 + 64909025019891545058702 * α ^ 14 - 1621590589357829572680 * α ^ 15 - 347824272218530328424 * α ^ 16 - 21365270620680629952 * α ^ 17 - 794207858493279744 * α ^ 18 - 20077534583212032 * α ^ 19 - 355351304655360 * α ^ 20 - 4364532094464 * α ^ 21 - 35609836032 * α ^ 22 - 174127104 * α ^ 23 - 387072 * α ^ 24) / (2011529617309570312500000 * (3 + α) ^ 12) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (750669183453805732727050781250 + 3020533706655215263366699218750 * α + 5564839729610338783264160156250 * α ^ 2 + 6204652935907732786560058593750 * α ^ 3 + 4659850847351595430480957031250 * α ^ 4 + 2480313988118708551463378906250 * α ^ 5 + 956953438533800725637460937500 * α ^ 6 + 267988469385291406396875000000 * α ^ 7 + 53061280626889862612388984375 * α ^ 8 + 6649776660279075672227540625 * α ^ 9 + 67029306131497703210255025 * α ^ 10 - 797547671168471728584421521 * α ^ 11 + 69793209950586805764791132 * α ^ 12 + 1582701213221515173844854 * α ^ 13 + 64909025019891545058702 * α ^ 14 - 1621590589357829572680 * α ^ 15 - 347824272218530328424 * α ^ 16 - 21365270620680629952 * α ^ 17 - 794207858493279744 * α ^ 18 - 20077534583212032 * α ^ 19 - 355351304655360 * α ^ 20 - 4364532094464 * α ^ 21 - 35609836032 * α ^ 22 - 174127104 * α ^ 23 - 387072 * α ^ 24) / (2011529617309570312500000 * (3 + α) ^ 12) := div_pos hP (by positivity)
  linarith
end Sendov.B26_27
