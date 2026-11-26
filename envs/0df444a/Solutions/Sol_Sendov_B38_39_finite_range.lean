-- Prove2me | solution 1 for Sendov.B38_39.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:12:28.145669+00:00
-- url     : https://prove2.me/submissions/b20f078f-f0e4-4835-88ee-92553138ac86

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree38_39
import Theorems.Thm_Sendov_B38_39_M_lo
import Theorems.Thm_Sendov_B38_39_M_hi
import Theorems.Thm_Sendov_B38_39_A_hi
import Theorems.Thm_Sendov_B38_39_c_lo_nonneg
import Theorems.Thm_Sendov_B38_39_integral_lo
import Theorems.Thm_Sendov_B38_39_P_pos
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
open Sendov.B38_39
set_option maxHeartbeats 2000000
namespace Sendov.B38_39
theorem _root_.solution {n : ℕ} (h0 : 38 ≤ n) (h1 : n ≤ 39) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 17 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (39 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (39 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 38) (n := n) (n₁ := 39) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((38 : ℕ) : ℝ) - 4 = 34 by norm_num] at hb
  rw [show (34 : ℝ) / 2 = ((17 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 37) + 1 / (4 * 37 * (3 + α))
      + (1 - 2 * α / 38) ^ 2 * 39 * 38 * (39 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 37 * (3 + α)) ^ 17))
      = 1 - (263016241667210021671084890841481617690003189110 + 1586061041777522258785370750920508059260325100670 * α + 4515569002916763022083813591656453793545843463960 * α ^ 2 + 8064535450447153538886731843043227730967854436080 * α ^ 3 + 10124049292126400106014356225197947036232792604485 * α ^ 4 + 9486490487762873429871569630238934346081556621609 * α ^ 5 + 6875502816855646349457849536822502570739478645343 * α ^ 6 + 3940536916491738744952644524802984325688545318839 * α ^ 7 + 1810118648803944257004276579444295893576974412957 * α ^ 8 + 671223601039568220250335587923837679954504671929 * α ^ 9 + 201302327242382412835780103712068254297083069927 * α ^ 10 + 48665320464285286858138805925504857552220130935 * α ^ 11 + 9395447364524194147939717327946455319249576385 * α ^ 12 + 1422463731757903542558687467068487748999154005 * α ^ 13 + 162936488968328754409221779604516446092275015 * α ^ 14 + 12804246766409474561270894860455521523191007 * α ^ 15 + 216069416334011168489825518695466581657549 * α ^ 16 - 808211600142399392096627843592018139890543 * α ^ 17 + 38042736580603120168867477319356142859621 * α ^ 18 + 344373790265831271857444699712655317117 * α ^ 19 + 29315226870352164747186119924985775776 * α ^ 20 + 1247198097855472249813750976434442560 * α ^ 21 + 16662184536264199136681220318869840 * α ^ 22 - 1406905416514864930658623327447840 * α ^ 23 - 115154592405960528415597818779200 * α ^ 24 - 4877945634325956011421670432000 * α ^ 25 - 144681078013665355320791476480 * α ^ 26 - 3249838030348665967746429440 * α ^ 27 - 56982963376184696008104960 * α ^ 28 - 788738718851438284800000 * α ^ 29 - 8618882420705188376576 * α ^ 30 - 73677168662756319232 * α ^ 31 - 483260148118798336 * α ^ 32 - 2351449584959488 * α ^ 33 - 8003806560256 * α ^ 34 - 17023172608 * α ^ 35 - 17039360 * α ^ 36) / (944533280285743117909608355250454382800 * (3 + α) ^ 18) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (263016241667210021671084890841481617690003189110 + 1586061041777522258785370750920508059260325100670 * α + 4515569002916763022083813591656453793545843463960 * α ^ 2 + 8064535450447153538886731843043227730967854436080 * α ^ 3 + 10124049292126400106014356225197947036232792604485 * α ^ 4 + 9486490487762873429871569630238934346081556621609 * α ^ 5 + 6875502816855646349457849536822502570739478645343 * α ^ 6 + 3940536916491738744952644524802984325688545318839 * α ^ 7 + 1810118648803944257004276579444295893576974412957 * α ^ 8 + 671223601039568220250335587923837679954504671929 * α ^ 9 + 201302327242382412835780103712068254297083069927 * α ^ 10 + 48665320464285286858138805925504857552220130935 * α ^ 11 + 9395447364524194147939717327946455319249576385 * α ^ 12 + 1422463731757903542558687467068487748999154005 * α ^ 13 + 162936488968328754409221779604516446092275015 * α ^ 14 + 12804246766409474561270894860455521523191007 * α ^ 15 + 216069416334011168489825518695466581657549 * α ^ 16 - 808211600142399392096627843592018139890543 * α ^ 17 + 38042736580603120168867477319356142859621 * α ^ 18 + 344373790265831271857444699712655317117 * α ^ 19 + 29315226870352164747186119924985775776 * α ^ 20 + 1247198097855472249813750976434442560 * α ^ 21 + 16662184536264199136681220318869840 * α ^ 22 - 1406905416514864930658623327447840 * α ^ 23 - 115154592405960528415597818779200 * α ^ 24 - 4877945634325956011421670432000 * α ^ 25 - 144681078013665355320791476480 * α ^ 26 - 3249838030348665967746429440 * α ^ 27 - 56982963376184696008104960 * α ^ 28 - 788738718851438284800000 * α ^ 29 - 8618882420705188376576 * α ^ 30 - 73677168662756319232 * α ^ 31 - 483260148118798336 * α ^ 32 - 2351449584959488 * α ^ 33 - 8003806560256 * α ^ 34 - 17023172608 * α ^ 35 - 17039360 * α ^ 36) / (944533280285743117909608355250454382800 * (3 + α) ^ 18) := div_pos hP (by positivity)
  linarith
end Sendov.B38_39
