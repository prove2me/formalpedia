-- Prove2me | solution 1 for Sendov.B30_31.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:40.017547+00:00
-- url     : https://prove2.me/submissions/b9d09fac-5e1f-4ad5-9f34-3016e688d773

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31
import Theorems.Thm_Sendov_B30_31_M_lo
import Theorems.Thm_Sendov_B30_31_M_hi
import Theorems.Thm_Sendov_B30_31_A_hi
import Theorems.Thm_Sendov_B30_31_c_lo_nonneg
import Theorems.Thm_Sendov_B30_31_integral_lo
import Theorems.Thm_Sendov_B30_31_P_pos
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
open Sendov.B30_31
set_option maxHeartbeats 2000000
namespace Sendov.B30_31
theorem _root_.solution {n : ℕ} (h0 : 30 ≤ n) (h1 : n ≤ 31) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 15 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (31 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (31 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 30) (n := n) (n₁ := 31) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((30 : ℕ) : ℝ) - 4 = 26 by norm_num] at hb
  rw [show (26 : ℝ) / 2 = ((13 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 29) + 1 / (4 * 29 * (3 + α))
      + (1 - 2 * α / 30) ^ 2 * 31 * 30 * (31 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 29 * (3 + α)) ^ 13))
      = 1 - (586577450963685326737168897370707500 + 2753132994648490979146101875384719500 * α + 5996201651556610186353013706234776680 * α ^ 2 + 8030975436338556704707041798612128472 * α ^ 3 + 7388055615126493367424454764006350082 * α ^ 4 + 4936598337528514606768767094265091378 * α ^ 5 + 2469192037754886771172170203022293214 * α ^ 6 + 938102920031818441360780570553215590 * α ^ 7 + 271392183919032658980825616039479546 * α ^ 8 + 59155996945930238392567631443933866 * α ^ 9 + 9399459563896087929210688264754844 * α ^ 10 + 974977535533292148502665510758532 * α ^ 11 + 10861549420545366403779627757839 * α ^ 12 - 92622867478166716461279291384369 * α ^ 13 + 6300099969105231240951104525763 * α ^ 14 + 117642575887863777951373952647 * α ^ 15 + 6754895556059983986318667916 * α ^ 16 + 94553344499679709104836184 * α ^ 17 - 13437772607038842242965408 * α ^ 18 - 1178131104153353973775376 * α ^ 19 - 53368378574787271805184 * α ^ 20 - 1629770789867125896192 * α ^ 21 - 35941441812526263552 * α ^ 22 - 584181453145681152 * α ^ 23 - 6973783723783168 * α ^ 24 - 59692780623872 * α ^ 25 - 347727077376 * α ^ 26 - 1237127168 * α ^ 27 - 2031616 * α ^ 28) / (172881045887035525441599708000 * (3 + α) ^ 14) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (586577450963685326737168897370707500 + 2753132994648490979146101875384719500 * α + 5996201651556610186353013706234776680 * α ^ 2 + 8030975436338556704707041798612128472 * α ^ 3 + 7388055615126493367424454764006350082 * α ^ 4 + 4936598337528514606768767094265091378 * α ^ 5 + 2469192037754886771172170203022293214 * α ^ 6 + 938102920031818441360780570553215590 * α ^ 7 + 271392183919032658980825616039479546 * α ^ 8 + 59155996945930238392567631443933866 * α ^ 9 + 9399459563896087929210688264754844 * α ^ 10 + 974977535533292148502665510758532 * α ^ 11 + 10861549420545366403779627757839 * α ^ 12 - 92622867478166716461279291384369 * α ^ 13 + 6300099969105231240951104525763 * α ^ 14 + 117642575887863777951373952647 * α ^ 15 + 6754895556059983986318667916 * α ^ 16 + 94553344499679709104836184 * α ^ 17 - 13437772607038842242965408 * α ^ 18 - 1178131104153353973775376 * α ^ 19 - 53368378574787271805184 * α ^ 20 - 1629770789867125896192 * α ^ 21 - 35941441812526263552 * α ^ 22 - 584181453145681152 * α ^ 23 - 6973783723783168 * α ^ 24 - 59692780623872 * α ^ 25 - 347727077376 * α ^ 26 - 1237127168 * α ^ 27 - 2031616 * α ^ 28) / (172881045887035525441599708000 * (3 + α) ^ 14) := div_pos hP (by positivity)
  linarith
end Sendov.B30_31
