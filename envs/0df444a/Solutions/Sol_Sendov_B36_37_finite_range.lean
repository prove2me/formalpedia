-- Prove2me | solution 1 for Sendov.B36_37.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:12:22.389383+00:00
-- url     : https://prove2.me/submissions/e5dfb929-8017-4740-bfdb-8fcc3c66cb32

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37
import Theorems.Thm_Sendov_B36_37_M_lo
import Theorems.Thm_Sendov_B36_37_M_hi
import Theorems.Thm_Sendov_B36_37_A_hi
import Theorems.Thm_Sendov_B36_37_c_lo_nonneg
import Theorems.Thm_Sendov_B36_37_integral_lo
import Theorems.Thm_Sendov_B36_37_P_pos
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
open Sendov.B36_37
set_option maxHeartbeats 2000000
namespace Sendov.B36_37
theorem _root_.solution {n : ℕ} (h0 : 36 ≤ n) (h1 : n ≤ 37) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 17 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (37 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (37 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 36) (n := n) (n₁ := 37) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((36 : ℕ) : ℝ) - 4 = 32 by norm_num] at hb
  rw [show (32 : ℝ) / 2 = ((16 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 35) + 1 / (4 * 35 * (3 + α))
      + (1 - 2 * α / 36) ^ 2 * 37 * 36 * (37 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 35 * (3 + α)) ^ 16))
      = 1 - (1340862494179159723457439116979158935546875000 + 7637969043915714340759947223349395751953125000 * α + 20469159372189815097433030931483526306152343750 * α ^ 2 + 34274361726863699928017616105749597900390625000 * α ^ 3 + 40158420010659405404629812835302538476562500000 * α ^ 4 + 34937401402816329855420946112276054381835937500 * α ^ 5 + 23367211725435618964676169025739806953662109375 * α ^ 6 + 12270122821734134505495363628244218847460937500 * α ^ 7 + 5119554315996410501630574472803506399777343750 * α ^ 8 + 1706085086162412699720364430591688420225000000 * α ^ 9 + 453657266969080072299236418096329864193140625 * α ^ 10 + 95512498825559724167251930963289431001100000 * α ^ 11 + 15651081746907280778533576463846724310987500 * α ^ 12 + 1925946170421648313592236215225863164072500 * α ^ 13 + 160780952585487184902439630853241164106375 * α ^ 14 + 2481149473011100292550908813010287159220 * α ^ 15 - 11166042731030257542258130633810209326742 * α ^ 16 + 567791382062622839648458479091876877544 * α ^ 17 + 6430218988186661251397393995576293933 * α ^ 18 + 498747834176692841464289681241746784 * α ^ 19 + 18702443537088721760797370916939480 * α ^ 20 + 57367909378421946482804755695328 * α ^ 21 - 35467391809924321679454804549376 * α ^ 22 - 2344076836762407866768807250432 * α ^ 23 - 91095016683709754039240857216 * α ^ 24 - 2528503186830718445641541120 * α ^ 25 - 53176733671797993730857984 * α ^ 26 - 866597180873027929669632 * α ^ 27 - 11005160172719761434624 * α ^ 28 - 108265710516964073472 * α ^ 29 - 810954254409318400 * α ^ 30 - 4477829562761216 * α ^ 31 - 17204805009408 * α ^ 32 - 41120301056 * α ^ 33 - 46071808 * α ^ 34) / (14484306327350467025497631835937500000 * (3 + α) ^ 17) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (1340862494179159723457439116979158935546875000 + 7637969043915714340759947223349395751953125000 * α + 20469159372189815097433030931483526306152343750 * α ^ 2 + 34274361726863699928017616105749597900390625000 * α ^ 3 + 40158420010659405404629812835302538476562500000 * α ^ 4 + 34937401402816329855420946112276054381835937500 * α ^ 5 + 23367211725435618964676169025739806953662109375 * α ^ 6 + 12270122821734134505495363628244218847460937500 * α ^ 7 + 5119554315996410501630574472803506399777343750 * α ^ 8 + 1706085086162412699720364430591688420225000000 * α ^ 9 + 453657266969080072299236418096329864193140625 * α ^ 10 + 95512498825559724167251930963289431001100000 * α ^ 11 + 15651081746907280778533576463846724310987500 * α ^ 12 + 1925946170421648313592236215225863164072500 * α ^ 13 + 160780952585487184902439630853241164106375 * α ^ 14 + 2481149473011100292550908813010287159220 * α ^ 15 - 11166042731030257542258130633810209326742 * α ^ 16 + 567791382062622839648458479091876877544 * α ^ 17 + 6430218988186661251397393995576293933 * α ^ 18 + 498747834176692841464289681241746784 * α ^ 19 + 18702443537088721760797370916939480 * α ^ 20 + 57367909378421946482804755695328 * α ^ 21 - 35467391809924321679454804549376 * α ^ 22 - 2344076836762407866768807250432 * α ^ 23 - 91095016683709754039240857216 * α ^ 24 - 2528503186830718445641541120 * α ^ 25 - 53176733671797993730857984 * α ^ 26 - 866597180873027929669632 * α ^ 27 - 11005160172719761434624 * α ^ 28 - 108265710516964073472 * α ^ 29 - 810954254409318400 * α ^ 30 - 4477829562761216 * α ^ 31 - 17204805009408 * α ^ 32 - 41120301056 * α ^ 33 - 46071808 * α ^ 34) / (14484306327350467025497631835937500000 * (3 + α) ^ 17) := div_pos hP (by positivity)
  linarith
end Sendov.B36_37
