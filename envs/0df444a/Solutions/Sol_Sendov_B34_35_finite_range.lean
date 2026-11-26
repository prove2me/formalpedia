-- Prove2me | solution 1 for Sendov.B34_35.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:12:13.737787+00:00
-- url     : https://prove2.me/submissions/78566151-f16a-4ab7-87a5-71cd72896bc5

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree34_35
import Theorems.Thm_Sendov_B34_35_M_lo
import Theorems.Thm_Sendov_B34_35_M_hi
import Theorems.Thm_Sendov_B34_35_A_hi
import Theorems.Thm_Sendov_B34_35_c_lo_nonneg
import Theorems.Thm_Sendov_B34_35_integral_lo
import Theorems.Thm_Sendov_B34_35_P_pos
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
open Sendov.B34_35
set_option maxHeartbeats 2000000
namespace Sendov.B34_35
theorem _root_.solution {n : ℕ} (h0 : 34 ≤ n) (h1 : n ≤ 35) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 17 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (35 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (35 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 34) (n := n) (n₁ := 35) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((34 : ℕ) : ℝ) - 4 = 30 by norm_num] at hb
  rw [show (30 : ℝ) / 2 = ((15 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 33) + 1 / (4 * 33 * (3 + α))
      + (1 - 2 * α / 34) ^ 2 * 35 * 34 * (35 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 33 * (3 + α)) ^ 15))
      = 1 - (13399266531718143561671329774091404024125 + 71849885492802810816842838949259978576823 * α + 180538945319091116404922710783631485776255 * α ^ 2 + 282156930875912547195503056499665223632869 * α ^ 3 + 306955881947816717076752055353611201997433 * α ^ 4 + 246444353252723432574425088492703243027965 * α ^ 5 + 151019226036657912949719936683240321200053 * α ^ 6 + 72028327083715746440304318235594953916857 * α ^ 7 + 27007117326925331098314143315441103261561 * α ^ 8 + 7979024241553623900285784858349597089245 * α ^ 9 + 1847320854708526473676328223562198887417 * α ^ 10 + 329938708337757813561795624655269556461 * α ^ 11 + 43878641971714608549212527982241857715 * α ^ 12 + 3911666704610568428372170990877699643 * α ^ 13 + 54464632768848512857832724331386693 * α ^ 14 - 300202584430678770107735269889128119 * α ^ 15 + 16644540127319447720784804793743786 * α ^ 16 + 228891055611380679685401624709920 * α ^ 17 + 16200353115196577039237473724202 * α ^ 18 + 510663548855848557629648901888 * α ^ 19 - 6873476290889727146869228680 * α ^ 20 - 1591901557063130972106786240 * α ^ 21 - 90385492060860172817322528 * α ^ 22 - 3241298369821124224491264 * α ^ 23 - 83924819944658782911360 * α ^ 24 - 1639999868886062272512 * α ^ 25 - 24549687196522919424 * α ^ 26 - 281209623855906816 * α ^ 27 - 2429673447720960 * α ^ 28 - 15359508856832 * α ^ 29 - 67149078528 * α ^ 30 - 181665792 * α ^ 31 - 229376 * α ^ 32) / (435539996816352082589992870143936 * (3 + α) ^ 16) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (13399266531718143561671329774091404024125 + 71849885492802810816842838949259978576823 * α + 180538945319091116404922710783631485776255 * α ^ 2 + 282156930875912547195503056499665223632869 * α ^ 3 + 306955881947816717076752055353611201997433 * α ^ 4 + 246444353252723432574425088492703243027965 * α ^ 5 + 151019226036657912949719936683240321200053 * α ^ 6 + 72028327083715746440304318235594953916857 * α ^ 7 + 27007117326925331098314143315441103261561 * α ^ 8 + 7979024241553623900285784858349597089245 * α ^ 9 + 1847320854708526473676328223562198887417 * α ^ 10 + 329938708337757813561795624655269556461 * α ^ 11 + 43878641971714608549212527982241857715 * α ^ 12 + 3911666704610568428372170990877699643 * α ^ 13 + 54464632768848512857832724331386693 * α ^ 14 - 300202584430678770107735269889128119 * α ^ 15 + 16644540127319447720784804793743786 * α ^ 16 + 228891055611380679685401624709920 * α ^ 17 + 16200353115196577039237473724202 * α ^ 18 + 510663548855848557629648901888 * α ^ 19 - 6873476290889727146869228680 * α ^ 20 - 1591901557063130972106786240 * α ^ 21 - 90385492060860172817322528 * α ^ 22 - 3241298369821124224491264 * α ^ 23 - 83924819944658782911360 * α ^ 24 - 1639999868886062272512 * α ^ 25 - 24549687196522919424 * α ^ 26 - 281209623855906816 * α ^ 27 - 2429673447720960 * α ^ 28 - 15359508856832 * α ^ 29 - 67149078528 * α ^ 30 - 181665792 * α ^ 31 - 229376 * α ^ 32) / (435539996816352082589992870143936 * (3 + α) ^ 16) := div_pos hP (by positivity)
  linarith
end Sendov.B34_35
