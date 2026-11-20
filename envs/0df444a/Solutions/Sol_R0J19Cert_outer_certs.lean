-- Prove2me | solution 1 for R0J19Cert.outer_certs
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:50:26.271783+00:00
-- url     : https://prove2.me/submissions/17909bde-6c85-4a68-817e-1a1f6aab1a48

import Definitions.Def_r0j19_cert_core

open R0J19Cert

private theorem aux_W0_cert_16_ok : checkW0Go h_16 23 A1_num W0_cert_16 = true := by decide +kernel
private theorem aux_Kers_16_ok : checkKersAll 2 hy_8 h_16 0 Kers_16 = true := by decide +kernel
private theorem aux_W0_cert_48_ok : checkW0Go h_48 67 A1_num W0_cert_48 = true := by decide +kernel
private theorem aux_Kers_48_ok : checkKersAll 3 hy_16 h_48 0 Kers_48 = true := by decide +kernel
private theorem aux_SJ_b1_g0_ok : checkSJ8Go t0_b1 810770400 h_16 hy_8 err55_8 err110_8 2 0 55 false Ker_16_0 Ker_16_1 Ker_16_2 Ker_16_3 Ker_16_4 Ker_16_5 Ker_16_6 Ker_16_7 70 [] [] Jg_b1_0 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_Jsum_b1_ok : checkJ1Sum Jg_b1_0 Jc_b1.reverse = true := by decide +kernel
private theorem aux_JW_b1_ok : checkJWin4 Jc_b1 Jw_b1 = true := by decide +kernel
private theorem aux_Sl_b1_ok : checkSlices 8 4 W0_cert_16 Jw_b1 = true := by decide +kernel
private theorem aux_SJ_b2_g0_ok : checkSJ8Go t0_b2 810770400 h_48 hy_16 err55_16 err110_16 3 24 80 false Ker_48_0 Ker_48_1 Ker_48_2 Ker_48_3 Ker_48_4 Ker_48_5 Ker_48_6 Ker_48_7 127 Bdry_b2_8 [] Jg_b2_0 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_SJ_b2_g1_ok : checkSJ8Go t0_b2 854994240 h_48 hy_16 err55_16 err110_16 3 0 80 true Ker_48_8 Ker_48_9 Ker_48_10 Ker_48_11 Ker_48_12 Ker_48_13 Ker_48_14 Ker_48_15 127 [] Bdry_b2_8 Jg_b2_1 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_Jsum_b2_ok : checkJ2Sum Jg_b2_0 Jg_b2_1 Jc_b2.reverse = true := by decide +kernel
private theorem aux_JW_b2_ok : checkJWin1 Jc_b2 Jw_b2 = true := by decide +kernel
private theorem aux_Sl_b2_ok : checkSlices 13 1 W0_cert_48 Jw_b2 = true := by decide +kernel
private theorem aux_SJ_b4_g0_ok : checkSJ8Go t0_b4 810770400 h_48 hy_16 err55_16 err110_16 3 24 90 false Ker_48_0 Ker_48_1 Ker_48_2 Ker_48_3 Ker_48_4 Ker_48_5 Ker_48_6 Ker_48_7 137 Bdry_b4_8 [] Jg_b4_0 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_SJ_b4_g1_ok : checkSJ8Go t0_b4 854994240 h_48 hy_16 err55_16 err110_16 3 0 90 true Ker_48_8 Ker_48_9 Ker_48_10 Ker_48_11 Ker_48_12 Ker_48_13 Ker_48_14 Ker_48_15 137 [] Bdry_b4_8 Jg_b4_1 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_Jsum_b4_ok : checkJ2Sum Jg_b4_0 Jg_b4_1 Jc_b4.reverse = true := by decide +kernel
private theorem aux_JW_b4_ok : checkJWin1 Jc_b4 Jw_b4 = true := by decide +kernel
private theorem aux_Sl_b4_ok : checkSlices 23 1 W0_cert_48 Jw_b4 = true := by decide +kernel
private theorem aux_SJ_b5_g0_ok : checkSJ8Go t0_b5 810770400 h_16 hy_8 err55_8 err110_8 2 0 75 false Ker_16_0 Ker_16_1 Ker_16_2 Ker_16_3 Ker_16_4 Ker_16_5 Ker_16_6 Ker_16_7 90 [] [] Jg_b5_0 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_Jsum_b5_ok : checkJ1Sum Jg_b5_0 Jc_b5.reverse = true := by decide +kernel
private theorem aux_JW_b5_ok : checkJWin4 Jc_b5 Jw_b5 = true := by decide +kernel
private theorem aux_Sl_b5_ok : checkSlices 13 4 W0_cert_16 Jw_b5 = true := by decide +kernel

theorem solution :
  checkW0Go h_16 23 A1_num W0_cert_16 = true ∧
  checkKersAll 2 hy_8 h_16 0 Kers_16 = true ∧
  checkW0Go h_48 67 A1_num W0_cert_48 = true ∧
  checkKersAll 3 hy_16 h_48 0 Kers_48 = true ∧
  checkSJ8Go t0_b1 810770400 h_16 hy_8 err55_8 err110_8 2 0 55 false Ker_16_0 Ker_16_1 Ker_16_2 Ker_16_3 Ker_16_4 Ker_16_5 Ker_16_6 Ker_16_7 70 [] [] Jg_b1_0 [] [] [] [] [] [] [] [] = true ∧
  checkJ1Sum Jg_b1_0 Jc_b1.reverse = true ∧
  checkJWin4 Jc_b1 Jw_b1 = true ∧
  checkSlices 8 4 W0_cert_16 Jw_b1 = true ∧
  checkSJ8Go t0_b2 810770400 h_48 hy_16 err55_16 err110_16 3 24 80 false Ker_48_0 Ker_48_1 Ker_48_2 Ker_48_3 Ker_48_4 Ker_48_5 Ker_48_6 Ker_48_7 127 Bdry_b2_8 [] Jg_b2_0 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b2 854994240 h_48 hy_16 err55_16 err110_16 3 0 80 true Ker_48_8 Ker_48_9 Ker_48_10 Ker_48_11 Ker_48_12 Ker_48_13 Ker_48_14 Ker_48_15 127 [] Bdry_b2_8 Jg_b2_1 [] [] [] [] [] [] [] [] = true ∧
  checkJ2Sum Jg_b2_0 Jg_b2_1 Jc_b2.reverse = true ∧
  checkJWin1 Jc_b2 Jw_b2 = true ∧
  checkSlices 13 1 W0_cert_48 Jw_b2 = true ∧
  checkSJ8Go t0_b4 810770400 h_48 hy_16 err55_16 err110_16 3 24 90 false Ker_48_0 Ker_48_1 Ker_48_2 Ker_48_3 Ker_48_4 Ker_48_5 Ker_48_6 Ker_48_7 137 Bdry_b4_8 [] Jg_b4_0 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b4 854994240 h_48 hy_16 err55_16 err110_16 3 0 90 true Ker_48_8 Ker_48_9 Ker_48_10 Ker_48_11 Ker_48_12 Ker_48_13 Ker_48_14 Ker_48_15 137 [] Bdry_b4_8 Jg_b4_1 [] [] [] [] [] [] [] [] = true ∧
  checkJ2Sum Jg_b4_0 Jg_b4_1 Jc_b4.reverse = true ∧
  checkJWin1 Jc_b4 Jw_b4 = true ∧
  checkSlices 23 1 W0_cert_48 Jw_b4 = true ∧
  checkSJ8Go t0_b5 810770400 h_16 hy_8 err55_8 err110_8 2 0 75 false Ker_16_0 Ker_16_1 Ker_16_2 Ker_16_3 Ker_16_4 Ker_16_5 Ker_16_6 Ker_16_7 90 [] [] Jg_b5_0 [] [] [] [] [] [] [] [] = true ∧
  checkJ1Sum Jg_b5_0 Jc_b5.reverse = true ∧
  checkJWin4 Jc_b5 Jw_b5 = true ∧
  checkSlices 13 4 W0_cert_16 Jw_b5 = true :=
  ⟨aux_W0_cert_16_ok, aux_Kers_16_ok, aux_W0_cert_48_ok, aux_Kers_48_ok, aux_SJ_b1_g0_ok, aux_Jsum_b1_ok, aux_JW_b1_ok, aux_Sl_b1_ok, aux_SJ_b2_g0_ok, aux_SJ_b2_g1_ok, aux_Jsum_b2_ok, aux_JW_b2_ok, aux_Sl_b2_ok, aux_SJ_b4_g0_ok, aux_SJ_b4_g1_ok, aux_Jsum_b4_ok, aux_JW_b4_ok, aux_Sl_b4_ok, aux_SJ_b5_g0_ok, aux_Jsum_b5_ok, aux_JW_b5_ok, aux_Sl_b5_ok⟩
