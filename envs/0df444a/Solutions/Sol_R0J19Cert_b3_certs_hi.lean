-- Prove2me | solution 1 for R0J19Cert.b3_certs_hi
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:50:25.151185+00:00
-- url     : https://prove2.me/submissions/4515b3ba-1bac-4fcd-8e2f-57d8fe147ee2

import Definitions.Def_r0j19_cert_core

open R0J19Cert

private theorem aux_SJ_b3_g3_ok : checkSJ8Go t0_b3 854994240 h_288 hy_48 err55_48 err110_48 6 96 525 true Ker_288_24 Ker_288_25 Ker_288_26 Ker_288_27 Ker_288_28 Ker_288_29 Ker_288_30 Ker_288_31 812 Bdry_b3_32 Bdry_b3_24 Jg_b3_3 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_SJ_b3_g4_ok : checkSJ8Go t0_b3 869735520 h_288 hy_48 err55_48 err110_48 6 48 525 true Ker_288_32 Ker_288_33 Ker_288_34 Ker_288_35 Ker_288_36 Ker_288_37 Ker_288_38 Ker_288_39 812 Bdry_b3_40 Bdry_b3_32 Jg_b3_4 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_SJ_b3_g5_ok : checkSJ8Go t0_b3 884476800 h_288 hy_48 err55_48 err110_48 6 0 525 true Ker_288_40 Ker_288_41 Ker_288_42 Ker_288_43 Ker_288_44 Ker_288_45 Ker_288_46 Ker_288_47 812 [] Bdry_b3_40 Jg_b3_5 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_Jsum_b3_ok : checkJ6Sum Jg_b3_0 Jg_b3_1 Jg_b3_2 Jg_b3_3 Jg_b3_4 Jg_b3_5 Jc_b3.reverse = true := by decide +kernel
private theorem aux_JW_b3_ok : checkJWin1 Jc_b3 Jw_b3 = true := by decide +kernel
private theorem aux_Sl_b3_ok : checkSlices 128 1 W0_cert_288 Jw_b3 = true := by decide +kernel
private theorem aux_W0_cert_288_ok : checkW0Go h_288 397 A1_num W0_cert_288 = true := by decide +kernel
private theorem aux_Kers_288_ok : checkKersAll 6 hy_48 h_288 0 Kers_288 = true := by decide +kernel

theorem solution :
  checkSJ8Go t0_b3 854994240 h_288 hy_48 err55_48 err110_48 6 96 525 true Ker_288_24 Ker_288_25 Ker_288_26 Ker_288_27 Ker_288_28 Ker_288_29 Ker_288_30 Ker_288_31 812 Bdry_b3_32 Bdry_b3_24 Jg_b3_3 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b3 869735520 h_288 hy_48 err55_48 err110_48 6 48 525 true Ker_288_32 Ker_288_33 Ker_288_34 Ker_288_35 Ker_288_36 Ker_288_37 Ker_288_38 Ker_288_39 812 Bdry_b3_40 Bdry_b3_32 Jg_b3_4 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b3 884476800 h_288 hy_48 err55_48 err110_48 6 0 525 true Ker_288_40 Ker_288_41 Ker_288_42 Ker_288_43 Ker_288_44 Ker_288_45 Ker_288_46 Ker_288_47 812 [] Bdry_b3_40 Jg_b3_5 [] [] [] [] [] [] [] [] = true ∧
  checkJ6Sum Jg_b3_0 Jg_b3_1 Jg_b3_2 Jg_b3_3 Jg_b3_4 Jg_b3_5 Jc_b3.reverse = true ∧
  checkJWin1 Jc_b3 Jw_b3 = true ∧
  checkSlices 128 1 W0_cert_288 Jw_b3 = true ∧
  checkW0Go h_288 397 A1_num W0_cert_288 = true ∧
  checkKersAll 6 hy_48 h_288 0 Kers_288 = true :=
  ⟨aux_SJ_b3_g3_ok, aux_SJ_b3_g4_ok, aux_SJ_b3_g5_ok, aux_Jsum_b3_ok, aux_JW_b3_ok, aux_Sl_b3_ok, aux_W0_cert_288_ok, aux_Kers_288_ok⟩
