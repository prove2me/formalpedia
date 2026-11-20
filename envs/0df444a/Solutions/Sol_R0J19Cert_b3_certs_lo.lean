-- Prove2me | solution 1 for R0J19Cert.b3_certs_lo
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T10:50:24.067015+00:00
-- url     : https://prove2.me/submissions/270da4fe-3e77-422f-9abf-9722f384edb0

import Definitions.Def_r0j19_cert_core

open R0J19Cert

private theorem aux_SJ_b3_g0_ok : checkSJ8Go t0_b3 810770400 h_288 hy_48 err55_48 err110_48 6 240 525 false Ker_288_0 Ker_288_1 Ker_288_2 Ker_288_3 Ker_288_4 Ker_288_5 Ker_288_6 Ker_288_7 812 Bdry_b3_8 [] Jg_b3_0 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_SJ_b3_g1_ok : checkSJ8Go t0_b3 825511680 h_288 hy_48 err55_48 err110_48 6 192 525 true Ker_288_8 Ker_288_9 Ker_288_10 Ker_288_11 Ker_288_12 Ker_288_13 Ker_288_14 Ker_288_15 812 Bdry_b3_16 Bdry_b3_8 Jg_b3_1 [] [] [] [] [] [] [] [] = true := by decide +kernel
private theorem aux_SJ_b3_g2_ok : checkSJ8Go t0_b3 840252960 h_288 hy_48 err55_48 err110_48 6 144 525 true Ker_288_16 Ker_288_17 Ker_288_18 Ker_288_19 Ker_288_20 Ker_288_21 Ker_288_22 Ker_288_23 812 Bdry_b3_24 Bdry_b3_16 Jg_b3_2 [] [] [] [] [] [] [] [] = true := by decide +kernel

theorem solution :
  checkSJ8Go t0_b3 810770400 h_288 hy_48 err55_48 err110_48 6 240 525 false Ker_288_0 Ker_288_1 Ker_288_2 Ker_288_3 Ker_288_4 Ker_288_5 Ker_288_6 Ker_288_7 812 Bdry_b3_8 [] Jg_b3_0 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b3 825511680 h_288 hy_48 err55_48 err110_48 6 192 525 true Ker_288_8 Ker_288_9 Ker_288_10 Ker_288_11 Ker_288_12 Ker_288_13 Ker_288_14 Ker_288_15 812 Bdry_b3_16 Bdry_b3_8 Jg_b3_1 [] [] [] [] [] [] [] [] = true ∧
  checkSJ8Go t0_b3 840252960 h_288 hy_48 err55_48 err110_48 6 144 525 true Ker_288_16 Ker_288_17 Ker_288_18 Ker_288_19 Ker_288_20 Ker_288_21 Ker_288_22 Ker_288_23 812 Bdry_b3_24 Bdry_b3_16 Jg_b3_2 [] [] [] [] [] [] [] [] = true :=
  ⟨aux_SJ_b3_g0_ok, aux_SJ_b3_g1_ok, aux_SJ_b3_g2_ok⟩
