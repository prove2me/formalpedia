-- Prove2me | solution 1 for Sendov.B24_26.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:09.490667+00:00
-- url     : https://prove2.me/submissions/bf7bd179-b757-4725-93e6-b8ba6193c521

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
import Theorems.Thm_Sendov_B24_26_M_lo
import Theorems.Thm_Sendov_B24_26_M_hi
import Theorems.Thm_Sendov_B24_26_A_hi
import Theorems.Thm_Sendov_B24_26_c_lo_nonneg
import Theorems.Thm_Sendov_B24_26_integral_lo
import Theorems.Thm_Sendov_B24_26_P_pos
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
open Sendov.B24_26
set_option maxHeartbeats 2000000
namespace Sendov.B24_26
theorem _root_.solution {n : ℕ} (h0 : 24 ≤ n) (h1 : n ≤ 26) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 25 / 2 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (26 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (26 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 24) (n := n) (n₁ := 26) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((24 : ℕ) : ℝ) - 4 = 20 by norm_num] at hb
  rw [show (20 : ℝ) / 2 = ((10 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 23) + 1 / (4 * 23 * (3 + α))
      + (1 - 2 * α / 25) ^ 2 * 26 * 25 * (26 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 23 * (3 + α)) ^ 10))
      = 1 - (874071004010582953643568750 + 3221297610086019399669004500 * α + 5386914463346812349691460974 * α ^ 2 + 5391225879978445091101054368 * α ^ 3 + 3582299145670361769507272658 * α ^ 4 + 1654127651781089540379647100 * α ^ 5 + 537462463626302644652842710 * α ^ 6 + 120043033655516749475390448 * α ^ 7 + 16184849120135434020794931 * α ^ 8 - 222784389930881498880726 * α ^ 9 - 2725770297915674501126913 * α ^ 10 + 248640476833385673099320 * α ^ 11 + 6386094327528944247792 * α ^ 12 + 230085309479261626272 * α ^ 13 - 10099884196228450032 * α ^ 14 - 1569527054513950464 * α ^ 15 - 87896838917715456 * α ^ 16 - 2989402709094912 * α ^ 17 - 67703370254592 * α ^ 18 - 1033617561600 * α ^ 19 - 10281172992 * α ^ 20 - 60432384 * α ^ 21 - 159744 * α ^ 22) / (7109199446723183525100 * (3 + α) ^ 11) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (874071004010582953643568750 + 3221297610086019399669004500 * α + 5386914463346812349691460974 * α ^ 2 + 5391225879978445091101054368 * α ^ 3 + 3582299145670361769507272658 * α ^ 4 + 1654127651781089540379647100 * α ^ 5 + 537462463626302644652842710 * α ^ 6 + 120043033655516749475390448 * α ^ 7 + 16184849120135434020794931 * α ^ 8 - 222784389930881498880726 * α ^ 9 - 2725770297915674501126913 * α ^ 10 + 248640476833385673099320 * α ^ 11 + 6386094327528944247792 * α ^ 12 + 230085309479261626272 * α ^ 13 - 10099884196228450032 * α ^ 14 - 1569527054513950464 * α ^ 15 - 87896838917715456 * α ^ 16 - 2989402709094912 * α ^ 17 - 67703370254592 * α ^ 18 - 1033617561600 * α ^ 19 - 10281172992 * α ^ 20 - 60432384 * α ^ 21 - 159744 * α ^ 22) / (7109199446723183525100 * (3 + α) ^ 11) := div_pos hP (by positivity)
  linarith
end Sendov.B24_26
