-- Prove2me | solution 1 for Sendov.B32_33.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:11:50.869579+00:00
-- url     : https://prove2.me/submissions/a1ed87a6-df42-43ab-8766-0beeb4e49739

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33
import Theorems.Thm_Sendov_B32_33_M_lo
import Theorems.Thm_Sendov_B32_33_M_hi
import Theorems.Thm_Sendov_B32_33_A_hi
import Theorems.Thm_Sendov_B32_33_c_lo_nonneg
import Theorems.Thm_Sendov_B32_33_integral_lo
import Theorems.Thm_Sendov_B32_33_P_pos
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
open Sendov.B32_33
set_option maxHeartbeats 2000000
namespace Sendov.B32_33
theorem _root_.solution {n : ℕ} (h0 : 32 ≤ n) (h1 : n ≤ 33) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 16 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (33 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (33 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 32) (n := n) (n₁ := 33) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((32 : ℕ) : ℝ) - 4 = 28 by norm_num] at hb
  rw [show (28 : ℝ) / 2 = ((14 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 31) + 1 / (4 * 31 * (3 + α))
      + (1 - 2 * α / 32) ^ 2 * 33 * 32 * (33 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 31 * (3 + α)) ^ 14))
      = 1 - (383977583360819576313951392966054557440 + 1930634984998770141470327139790256873760 * α + 4528139655529657241697903448404234220551 * α ^ 2 + 6571116743547522810411224078221219285242 * α ^ 3 + 6597373572981213714180223077765169741761 * α ^ 4 + 4853145290868457132481352533313124037136 * α ^ 5 + 2701279688513765542055333848381676518287 * α ^ 6 + 1157769823809425762972955166775789744790 * α ^ 7 + 384826365482239087514233918976406892725 * α ^ 8 + 98972460520277767374027328895457052524 * α ^ 9 + 19429030643214541979169516429755259903 * α ^ 10 + 2812337464920293963928011188383752346 * α ^ 11 + 269412053495826821775011955678389445 * α ^ 12 + 3352473026131557768885960806993016 * α ^ 13 - 22950931900671630187087717249723635 * α ^ 14 + 1401665499631441401236402118586466 * α ^ 15 + 22766380179065358125804378947555 * α ^ 16 + 1462014916628262060084862591156 * α ^ 17 + 35132359566977040523019407180 * α ^ 18 - 1604603346728872922022402944 * α ^ 19 - 192243388845480689610974960 * α ^ 20 - 9672937893957196503857344 * α ^ 21 - 320523259524150064257216 * α ^ 22 - 7695435702924730354176 * α ^ 23 - 138216454665665111296 * α ^ 24 - 1869603872239262720 * α ^ 25 - 18853950116959232 * α ^ 26 - 137859411329024 * α ^ 27 - 692050472960 * α ^ 28 - 2136915968 * α ^ 29 - 3063808 * α ^ 30) / (37572885123356984842662119654400 * (3 + α) ^ 15) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (383977583360819576313951392966054557440 + 1930634984998770141470327139790256873760 * α + 4528139655529657241697903448404234220551 * α ^ 2 + 6571116743547522810411224078221219285242 * α ^ 3 + 6597373572981213714180223077765169741761 * α ^ 4 + 4853145290868457132481352533313124037136 * α ^ 5 + 2701279688513765542055333848381676518287 * α ^ 6 + 1157769823809425762972955166775789744790 * α ^ 7 + 384826365482239087514233918976406892725 * α ^ 8 + 98972460520277767374027328895457052524 * α ^ 9 + 19429030643214541979169516429755259903 * α ^ 10 + 2812337464920293963928011188383752346 * α ^ 11 + 269412053495826821775011955678389445 * α ^ 12 + 3352473026131557768885960806993016 * α ^ 13 - 22950931900671630187087717249723635 * α ^ 14 + 1401665499631441401236402118586466 * α ^ 15 + 22766380179065358125804378947555 * α ^ 16 + 1462014916628262060084862591156 * α ^ 17 + 35132359566977040523019407180 * α ^ 18 - 1604603346728872922022402944 * α ^ 19 - 192243388845480689610974960 * α ^ 20 - 9672937893957196503857344 * α ^ 21 - 320523259524150064257216 * α ^ 22 - 7695435702924730354176 * α ^ 23 - 138216454665665111296 * α ^ 24 - 1869603872239262720 * α ^ 25 - 18853950116959232 * α ^ 26 - 137859411329024 * α ^ 27 - 692050472960 * α ^ 28 - 2136915968 * α ^ 29 - 3063808 * α ^ 30) / (37572885123356984842662119654400 * (3 + α) ^ 15) := div_pos hP (by positivity)
  linarith
end Sendov.B32_33
