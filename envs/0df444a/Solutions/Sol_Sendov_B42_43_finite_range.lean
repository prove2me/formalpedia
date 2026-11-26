-- Prove2me | solution 1 for Sendov.B42_43.finite_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:12:54.885491+00:00
-- url     : https://prove2.me/submissions/af731121-fba8-4a42-b56e-0b159247a814

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree42_43
import Theorems.Thm_Sendov_B42_43_M_lo
import Theorems.Thm_Sendov_B42_43_M_hi
import Theorems.Thm_Sendov_B42_43_A_hi
import Theorems.Thm_Sendov_B42_43_c_lo_nonneg
import Theorems.Thm_Sendov_B42_43_integral_lo
import Theorems.Thm_Sendov_B42_43_P_pos
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
open Sendov.B42_43
set_option maxHeartbeats 2000000
namespace Sendov.B42_43
theorem _root_.solution {n : ℕ} (h0 : 42 ≤ n) (h1 : n ≤ 43) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hMn := alpha_le_half_M (n := n) (by omega) hfeas
  -- feasibility caps α at M n / 2, which for a low batch is sharper than the ambient α ≤ 17
  have hUn : α ≤ 17 := by
    have hcast : ((n : ℕ) : ℝ) ≤ (43 : ℝ) := by exact_mod_cast h1
    have hMle : M n ≤ (43 : ℝ) - 1 := by simp only [M]; linarith
    linarith [_hα']
  have hb := R_le_batch (n₀ := 42) (n := n) (n₁ := 43) (by norm_num) h0 h1 hα
    (c_lo_nonneg hα hUn) hfeas
  rw [show ((42 : ℕ) : ℝ) - 4 = 38 by norm_num] at hb
  rw [show (38 : ℝ) / 2 = ((19 : ℕ) : ℝ) by norm_num] at hb
  simp only [Real.rpow_natCast] at hb
  rw [integral_lo α hα, M_lo, M_hi, A_hi] at hb
  push_cast at hb
  have hid : (1 : ℝ) / 6 + 1 / (4 * (3 + α)) + 1 / (2 * 41) + 1 / (4 * 41 * (3 + α))
      + (1 - 2 * α / 42) ^ 2 * 43 * 42 * (43 - 2) / (4 * (3 + α))
        * (pev Nmomc α / ((Lc : ℝ) * (2 * 41 * (3 + α)) ^ 19))
      = 1 - (1280928413415314397834869540387070773955050164531041030 + 8579596886133703000731870831081948314922065693350883370 * α + 27292297105154921952287403075281892231896279402880100950 * α ^ 2 + 54824009941858550176912358984664841592247597016637905770 * α ^ 3 + 77993650469489645959523814188253045468476206212378807150 * α ^ 4 + 83524935090318289329452750100125758268073947901595075110 * α ^ 5 + 69864044339248988241671793073316243248508325653371578960 * α ^ 6 + 46735744905970337877740011413866843308996677044757141876 * α ^ 7 + 25392412342651970229153408582081225972535817324636108157 * α ^ 8 + 11314456845720888558092495939704512751963595258860145451 * α ^ 9 + 4156583831931947231874280330967249614130082308880369711 * α ^ 10 + 1260841374442113914894353137980805411382131606623222097 * α ^ 11 + 315103088046242389807187425423229491723179974811052320 * α ^ 12 + 64474796856269342035203905269807575254628539228620830 * α ^ 13 + 10677851103479065036063092086580878016800993639429844 * α ^ 14 + 1403715274370741006129430385190458757679221958797478 * α ^ 15 + 141371440744366093378881819780110077583832470458881 * α ^ 16 + 9967433380699679025437124999852577310642665327515 * α ^ 17 + 193067019640064558163668388981876117360705214251 * α ^ 18 - 526348205714148288340590540843861549545919252135 * α ^ 19 + 21747004181067783415574645835305370950903835816 * α ^ 20 + 112680245244072016728446540389593488784136590 * α ^ 21 + 11981738273725154350817268365041623637172994 * α ^ 22 + 613973728602142293085684365363276715529976 * α ^ 23 + 15948973394297291153786386954935347707464 * α ^ 24 - 107684213318232680083685034683113736832 * α ^ 25 - 31027964293347059199661593149947343808 * α ^ 26 - 1633467609886255958992085630289238016 * α ^ 27 - 55350060514047685232072125284311296 * α ^ 28 - 1399005645314407761350477999499264 * α ^ 29 - 27739113827411317709592921773056 * α ^ 30 - 440917774047260414297889849344 * α ^ 31 - 5667329623457291353154629632 * α ^ 32 - 58939961119748330433282048 * α ^ 33 - 492976521437911894081536 * α ^ 34 - 3273203375389549068288 * α ^ 35 - 16876898137105432576 * α ^ 36 - 65205684590477312 * α ^ 37 - 177752858296320 * α ^ 38 - 305048059904 * α ^ 39 - 247988224 * α ^ 40) / (508824949463896030944977981473879851039376800 * (3 + α) ^ 20) := by
    simp only [pev, Lc, Nmomc]
    push_cast
    field_simp
    ring
  rw [hid] at hb
  have hP := P_pos hα hUn
  have hq : 0 < (1280928413415314397834869540387070773955050164531041030 + 8579596886133703000731870831081948314922065693350883370 * α + 27292297105154921952287403075281892231896279402880100950 * α ^ 2 + 54824009941858550176912358984664841592247597016637905770 * α ^ 3 + 77993650469489645959523814188253045468476206212378807150 * α ^ 4 + 83524935090318289329452750100125758268073947901595075110 * α ^ 5 + 69864044339248988241671793073316243248508325653371578960 * α ^ 6 + 46735744905970337877740011413866843308996677044757141876 * α ^ 7 + 25392412342651970229153408582081225972535817324636108157 * α ^ 8 + 11314456845720888558092495939704512751963595258860145451 * α ^ 9 + 4156583831931947231874280330967249614130082308880369711 * α ^ 10 + 1260841374442113914894353137980805411382131606623222097 * α ^ 11 + 315103088046242389807187425423229491723179974811052320 * α ^ 12 + 64474796856269342035203905269807575254628539228620830 * α ^ 13 + 10677851103479065036063092086580878016800993639429844 * α ^ 14 + 1403715274370741006129430385190458757679221958797478 * α ^ 15 + 141371440744366093378881819780110077583832470458881 * α ^ 16 + 9967433380699679025437124999852577310642665327515 * α ^ 17 + 193067019640064558163668388981876117360705214251 * α ^ 18 - 526348205714148288340590540843861549545919252135 * α ^ 19 + 21747004181067783415574645835305370950903835816 * α ^ 20 + 112680245244072016728446540389593488784136590 * α ^ 21 + 11981738273725154350817268365041623637172994 * α ^ 22 + 613973728602142293085684365363276715529976 * α ^ 23 + 15948973394297291153786386954935347707464 * α ^ 24 - 107684213318232680083685034683113736832 * α ^ 25 - 31027964293347059199661593149947343808 * α ^ 26 - 1633467609886255958992085630289238016 * α ^ 27 - 55350060514047685232072125284311296 * α ^ 28 - 1399005645314407761350477999499264 * α ^ 29 - 27739113827411317709592921773056 * α ^ 30 - 440917774047260414297889849344 * α ^ 31 - 5667329623457291353154629632 * α ^ 32 - 58939961119748330433282048 * α ^ 33 - 492976521437911894081536 * α ^ 34 - 3273203375389549068288 * α ^ 35 - 16876898137105432576 * α ^ 36 - 65205684590477312 * α ^ 37 - 177752858296320 * α ^ 38 - 305048059904 * α ^ 39 - 247988224 * α ^ 40) / (508824949463896030944977981473879851039376800 * (3 + α) ^ 20) := div_pos hP (by positivity)
  linarith
end Sendov.B42_43
