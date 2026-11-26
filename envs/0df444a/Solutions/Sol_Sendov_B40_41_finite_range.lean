-- Prove2me | solution 1 for Sendov.B40_41.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:12:38.565522+00:00
-- url     : https://prove2.me/submissions/58146e00-4f30-4422-9f53-aee432407ec9

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
import Theorems.Thm_Sendov_B40_41_M_lo
import Theorems.Thm_Sendov_B40_41_M_hi
import Theorems.Thm_Sendov_B40_41_A_hi
import Theorems.Thm_Sendov_B40_41_c_lo_nonneg
import Theorems.Thm_Sendov_B40_41_integral_lo
import Theorems.Thm_Sendov_B40_41_P_pos
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
open Sendov.B40_41
set_option maxHeartbeats 2000000
namespace Sendov.B40_41
theorem _root_.solution {n : ℕ} (h0 : 40 ≤ n) (h1 : n ≤ 41) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 17 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (41 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (41 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 40) (n := n) (n₁ := 41) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((40 : ℕ) : ℝ) - 4 = 36 by norm_num] at hb
  rw [show (36 : ℝ) / 2 = ((18 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 39) + 1 / (4 * 39 * (3 + α))
      + (1 - 2 * α / 40) ^ 2 * 41 * 40 * (41 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 39 * (3 + α)) ^ 18))
      = 1 - (653328533869198792815460418567456328463360027860000 + 4157882298167732116226370617284188848212873011241200 * α + 12532182988010399386002617462745633312768152237121570 * α ^ 2 + 23778313854745445633723704693422676769304621097023060 * α ^ 3 + 31839691004956228828005033576674262680347642949789970 * α ^ 4 + 31966947875077850162540664582127534223677059725715480 * α ^ 5 + 24954452263842718944480719755732872419125467194310990 * α ^ 6 + 15498456398852386516930447507216103141023058978163900 * α ^ 7 + 7770525510255924837049186376423929043180641908035178 * α ^ 8 + 3172282421659051612506049390871943668830947112996128 * α ^ 9 + 1058580212642493803810630674822381941853484677345557 * α ^ 10 + 288603554681274589435804606029301359165948874522986 * α ^ 11 + 63964171378367904791712568423672278670444648520985 * α ^ 12 + 11403554558448059539985445321284291979921951939708 * α ^ 13 + 1604683068013899575897130419685118852646893739688 * α ^ 14 + 171973766788073602692262435759609700705097645552 * α ^ 15 + 12777319017916275759622043304057680904260665896 * α ^ 16 + 232511338229217727198624028718607742301689616 * α ^ 17 - 736152391583269859036039443814447014605197787 * α ^ 18 + 32344027389559443630831441714104468449897746 * α ^ 19 + 226192739078384191702850277844962783099369 * α ^ 20 + 21321388850847068435151126284573459826132 * α ^ 21 + 1002825060545767936823647697965569833484 * α ^ 22 + 20605096429138626101144518690493027136 * α ^ 23 - 588379321688541475027751329888140192 * α ^ 24 - 68916522458163479393324809629479808 * α ^ 25 - 3219999749177967431080752136593024 * α ^ 26 - 101984865798504570834320095942656 * α ^ 27 - 2433981075208899701339322164736 * α ^ 28 - 45526079756647968714698102784 * α ^ 29 - 678401876172921453922277376 * α ^ 30 - 8091691517611230731255808 * α ^ 31 - 76978691001245722632192 * α ^ 32 - 577480811034021101568 * α ^ 33 - 3345672064015171584 * α ^ 34 - 14456978064408576 * α ^ 35 - 43900332474368 * α ^ 36 - 83629441024 * α ^ 37 - 75235328 * α ^ 38) / (780218937072834586624023381831090266352000 * (3 + α) ^ 19) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (653328533869198792815460418567456328463360027860000 + 4157882298167732116226370617284188848212873011241200 * α + 12532182988010399386002617462745633312768152237121570 * α ^ 2 + 23778313854745445633723704693422676769304621097023060 * α ^ 3 + 31839691004956228828005033576674262680347642949789970 * α ^ 4 + 31966947875077850162540664582127534223677059725715480 * α ^ 5 + 24954452263842718944480719755732872419125467194310990 * α ^ 6 + 15498456398852386516930447507216103141023058978163900 * α ^ 7 + 7770525510255924837049186376423929043180641908035178 * α ^ 8 + 3172282421659051612506049390871943668830947112996128 * α ^ 9 + 1058580212642493803810630674822381941853484677345557 * α ^ 10 + 288603554681274589435804606029301359165948874522986 * α ^ 11 + 63964171378367904791712568423672278670444648520985 * α ^ 12 + 11403554558448059539985445321284291979921951939708 * α ^ 13 + 1604683068013899575897130419685118852646893739688 * α ^ 14 + 171973766788073602692262435759609700705097645552 * α ^ 15 + 12777319017916275759622043304057680904260665896 * α ^ 16 + 232511338229217727198624028718607742301689616 * α ^ 17 - 736152391583269859036039443814447014605197787 * α ^ 18 + 32344027389559443630831441714104468449897746 * α ^ 19 + 226192739078384191702850277844962783099369 * α ^ 20 + 21321388850847068435151126284573459826132 * α ^ 21 + 1002825060545767936823647697965569833484 * α ^ 22 + 20605096429138626101144518690493027136 * α ^ 23 - 588379321688541475027751329888140192 * α ^ 24 - 68916522458163479393324809629479808 * α ^ 25 - 3219999749177967431080752136593024 * α ^ 26 - 101984865798504570834320095942656 * α ^ 27 - 2433981075208899701339322164736 * α ^ 28 - 45526079756647968714698102784 * α ^ 29 - 678401876172921453922277376 * α ^ 30 - 8091691517611230731255808 * α ^ 31 - 76978691001245722632192 * α ^ 32 - 577480811034021101568 * α ^ 33 - 3345672064015171584 * α ^ 34 - 14456978064408576 * α ^ 35 - 43900332474368 * α ^ 36 - 83629441024 * α ^ 37 - 75235328 * α ^ 38) / (780218937072834586624023381831090266352000 * (3 + α) ^ 19) := div_pos hP (by positivity)
  linarith
end Sendov.B40_41
