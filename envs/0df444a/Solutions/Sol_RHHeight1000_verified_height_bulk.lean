-- Prove2me | solution 1 for RHHeight1000.verified_height_bulk
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:46:54.827388+00:00
-- url     : https://prove2.me/submissions/ca8d1efd-2f2d-40e8-833a-fe183a4f7afe

import Theorems.Thm_RHHeight1000_close_from_656_intervals_and_gram
import Theorems.Thm_RHHeight1000_certified_gram_sequence_655
import Theorems.Thm_RHHeight1000_em_prefix_0013
import Theorems.Thm_RHHeight1000_em_main_0014_0014
import Theorems.Thm_RHHeight1000_em_main_0015_0015
import Theorems.Thm_RHHeight1000_em_main_0016_0016
import Theorems.Thm_RHHeight1000_em_main_0017_0017
import Theorems.Thm_RHHeight1000_em_main_0018_0018
import Theorems.Thm_RHHeight1000_em_main_0019_0019
import Theorems.Thm_RHHeight1000_em_main_0020_0020
import Theorems.Thm_RHHeight1000_em_main_0021_0021
import Theorems.Thm_RHHeight1000_em_main_0022_0022
import Theorems.Thm_RHHeight1000_em_main_0023_0023
import Theorems.Thm_RHHeight1000_em_main_0024_0024
import Theorems.Thm_RHHeight1000_em_main_0025_0025
import Theorems.Thm_RHHeight1000_em_main_0026_0026
import Theorems.Thm_RHHeight1000_em_main_0027_0027
import Theorems.Thm_RHHeight1000_em_main_0028_0028
import Theorems.Thm_RHHeight1000_em_main_0029_0029
import Theorems.Thm_RHHeight1000_em_main_0030_0030
import Theorems.Thm_RHHeight1000_em_main_0031_0031
import Theorems.Thm_RHHeight1000_em_main_0032_0032
import Theorems.Thm_RHHeight1000_em_main_0033_0033
import Theorems.Thm_RHHeight1000_em_main_0034_0034
import Theorems.Thm_RHHeight1000_em_main_0035_0035
import Theorems.Thm_RHHeight1000_em_main_0036_0036
import Theorems.Thm_RHHeight1000_em_main_0037_0037
import Theorems.Thm_RHHeight1000_em_main_0038_0038
import Theorems.Thm_RHHeight1000_em_main_0039_0039
import Theorems.Thm_RHHeight1000_em_main_0040_0040
import Theorems.Thm_RHHeight1000_em_main_0041_0041
import Theorems.Thm_RHHeight1000_em_main_0042_0042
import Theorems.Thm_RHHeight1000_em_main_0043_0043
import Theorems.Thm_RHHeight1000_em_main_0044_0044
import Theorems.Thm_RHHeight1000_em_main_0045_0045
import Theorems.Thm_RHHeight1000_em_main_0046_0046
import Theorems.Thm_RHHeight1000_em_main_0047_0047
import Theorems.Thm_RHHeight1000_em_main_0048_0048
import Theorems.Thm_RHHeight1000_em_main_0049_0049
import Theorems.Thm_RHHeight1000_em_main_0050_0050
import Theorems.Thm_RHHeight1000_em_main_0051_0051
import Theorems.Thm_RHHeight1000_em_main_0052_0052
import Theorems.Thm_RHHeight1000_rs_main_0001_0026
import Theorems.Thm_RHHeight1000_rs_main_0027_0036
import Theorems.Thm_RHHeight1000_rs_main_0037_0060
import Theorems.Thm_RHHeight1000_rs_main_0061_0078
import Theorems.Thm_RHHeight1000_rs_main_0079_0096
import Theorems.Thm_RHHeight1000_rs_main_0097_0114
import Theorems.Thm_RHHeight1000_rs_main_0115_0132
import Theorems.Thm_RHHeight1000_rs_main_0133_0150
import Theorems.Thm_RHHeight1000_rs_main_0151_0168
import Theorems.Thm_RHHeight1000_rs_main_0169_0186
import Theorems.Thm_RHHeight1000_rs_main_0187_0204
import Theorems.Thm_RHHeight1000_rs_main_0205_0222
import Theorems.Thm_RHHeight1000_rs_main_0223_0240
import Theorems.Thm_RHHeight1000_rs_main_0241_0252
import Theorems.Thm_RHHeight1000_rs_main_0253_0264
import Theorems.Thm_RHHeight1000_rs_main_0265_0276
import Theorems.Thm_RHHeight1000_rs_main_0277_0288
import Theorems.Thm_RHHeight1000_rs_main_0289_0300
import Theorems.Thm_RHHeight1000_rs_main_0301_0312
import Theorems.Thm_RHHeight1000_rs_main_0313_0324
import Theorems.Thm_RHHeight1000_rs_main_0325_0336
import Theorems.Thm_RHHeight1000_rs_main_0337_0348
import Theorems.Thm_RHHeight1000_rs_main_0349_0360
import Theorems.Thm_RHHeight1000_rs_main_0361_0372
import Theorems.Thm_RHHeight1000_rs_main_0373_0384
import Theorems.Thm_RHHeight1000_rs_main_0385_0396
import Theorems.Thm_RHHeight1000_rs_main_0397_0408
import Theorems.Thm_RHHeight1000_rs_main_0409_0420
import Theorems.Thm_RHHeight1000_rs_main_0421_0432
import Theorems.Thm_RHHeight1000_rs_main_0433_0438
import Theorems.Thm_RHHeight1000_rs_main_0439_0444
import Theorems.Thm_RHHeight1000_rs_main_0445_0450
import Theorems.Thm_RHHeight1000_rs_main_0451_0462
import Theorems.Thm_RHHeight1000_rs_main_0463_0474
import Theorems.Thm_RHHeight1000_rs_main_0475_0486
import Theorems.Thm_RHHeight1000_rs_main_0487_0498
import Theorems.Thm_RHHeight1000_rs_main_0499_0510
import Theorems.Thm_RHHeight1000_rs_main_0511_0522
import Theorems.Thm_RHHeight1000_rs_main_0523_0528
import Theorems.Thm_RHHeight1000_rs_main_0529_0540
import Theorems.Thm_RHHeight1000_rs_main_0541_0552
import Theorems.Thm_RHHeight1000_rs_main_0553_0564
import Theorems.Thm_RHHeight1000_rs_main_0565_0576
import Theorems.Thm_RHHeight1000_rs_main_0577_0588
import Theorems.Thm_RHHeight1000_rs_main_0589_0600
import Theorems.Thm_RHHeight1000_ordinary_batch4_inline_tail
open Zeta.Certificates
namespace Zeta.Certificates
theorem BatchSpec.joinHeight1000 {n₁ an ad bn bd n₂ cn cd en ed : ℕ} (h₁ : BatchSpec n₁ an ad bn bd)
    (h₂ : BatchSpec n₂ cn cd en ed) (hbd : Nat.ble 1 bd = true) (hcd : Nat.ble 1 cd = true)
    (hseam : Nat.ble (bn.mul cd) (cn.mul bd) = true) : BatchSpec (n₁ + n₂) an ad en ed := by
  obtain ⟨C, hCl, hCh, hCt⟩ := h₁
  obtain ⟨D, hDl, hDh, hDt⟩ := h₂
  have hC : C.intervals ≠ [] := by intro he; rw [he] at hCh; simp at hCh
  have hD : D.intervals ≠ [] := by intro he; rw [he] at hDh; simp at hDh
  refine ⟨C.append D (separated_of_endpoints hCt hDh
    (Enclosure.dec_le_dec bn bd cn cd rfl rfl hbd hcd hseam)), ?_, ?_, ?_⟩
  · simp [hCl, hDl]
  · rw [CertifiedZeroIntervals.append_intervals, List.head?_append_of_ne_nil _ hC, hCh]
  · rw [CertifiedZeroIntervals.append_intervals, List.getLast?_append_of_ne_nil _ hD, hDt]


end Zeta.Certificates


theorem solution (s : ℂ) (hz : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1) (hi : |s.im| ≤ 1000) : s.re = 1/2 := by
  have h13 : BatchSpec 13 1000 1000 60352 1000 := RHHeight1000.em_prefix_0013
  have h14 : BatchSpec 14 1000 1000 63102 1000 := BatchSpec.joinHeight1000 h13 RHHeight1000.em_main_0014_0014 rfl rfl rfl
  have h15 : BatchSpec 15 1000 1000 65801 1000 := BatchSpec.joinHeight1000 h14 RHHeight1000.em_main_0015_0015 rfl rfl rfl
  have h16 : BatchSpec 16 1000 1000 68454 1000 := BatchSpec.joinHeight1000 h15 RHHeight1000.em_main_0016_0016 rfl rfl rfl
  have h17 : BatchSpec 17 1000 1000 71064 1000 := BatchSpec.joinHeight1000 h16 RHHeight1000.em_main_0017_0017 rfl rfl rfl
  have h18 : BatchSpec 18 1000 1000 73635 1000 := BatchSpec.joinHeight1000 h17 RHHeight1000.em_main_0018_0018 rfl rfl rfl
  have h19 : BatchSpec 19 1000 1000 76170 1000 := BatchSpec.joinHeight1000 h18 RHHeight1000.em_main_0019_0019 rfl rfl rfl
  have h20 : BatchSpec 20 1000 1000 78672 1000 := BatchSpec.joinHeight1000 h19 RHHeight1000.em_main_0020_0020 rfl rfl rfl
  have h21 : BatchSpec 21 1000 1000 81143 1000 := BatchSpec.joinHeight1000 h20 RHHeight1000.em_main_0021_0021 rfl rfl rfl
  have h22 : BatchSpec 22 1000 1000 83585 1000 := BatchSpec.joinHeight1000 h21 RHHeight1000.em_main_0022_0022 rfl rfl rfl
  have h23 : BatchSpec 23 1000 1000 85999 1000 := BatchSpec.joinHeight1000 h22 RHHeight1000.em_main_0023_0023 rfl rfl rfl
  have h24 : BatchSpec 24 1000 1000 88388 1000 := BatchSpec.joinHeight1000 h23 RHHeight1000.em_main_0024_0024 rfl rfl rfl
  have h25 : BatchSpec 25 1000 1000 90753 1000 := BatchSpec.joinHeight1000 h24 RHHeight1000.em_main_0025_0025 rfl rfl rfl
  have h26 : BatchSpec 26 1000 1000 93095 1000 := BatchSpec.joinHeight1000 h25 RHHeight1000.em_main_0026_0026 rfl rfl rfl
  have h27 : BatchSpec 27 1000 1000 95415 1000 := BatchSpec.joinHeight1000 h26 RHHeight1000.em_main_0027_0027 rfl rfl rfl
  have h28 : BatchSpec 28 1000 1000 97714 1000 := BatchSpec.joinHeight1000 h27 RHHeight1000.em_main_0028_0028 rfl rfl rfl
  have h29 : BatchSpec 29 1000 1000 99995 1000 := BatchSpec.joinHeight1000 h28 RHHeight1000.em_main_0029_0029 rfl rfl rfl
  have h30 : BatchSpec 30 1000 1000 102256 1000 := BatchSpec.joinHeight1000 h29 RHHeight1000.em_main_0030_0030 rfl rfl rfl
  have h31 : BatchSpec 31 1000 1000 104500 1000 := BatchSpec.joinHeight1000 h30 RHHeight1000.em_main_0031_0031 rfl rfl rfl
  have h32 : BatchSpec 32 1000 1000 106726 1000 := BatchSpec.joinHeight1000 h31 RHHeight1000.em_main_0032_0032 rfl rfl rfl
  have h33 : BatchSpec 33 1000 1000 108936 1000 := BatchSpec.joinHeight1000 h32 RHHeight1000.em_main_0033_0033 rfl rfl rfl
  have h34 : BatchSpec 34 1000 1000 111131 1000 := BatchSpec.joinHeight1000 h33 RHHeight1000.em_main_0034_0034 rfl rfl rfl
  have h35 : BatchSpec 35 1000 1000 113311 1000 := BatchSpec.joinHeight1000 h34 RHHeight1000.em_main_0035_0035 rfl rfl rfl
  have h36 : BatchSpec 36 1000 1000 115476 1000 := BatchSpec.joinHeight1000 h35 RHHeight1000.em_main_0036_0036 rfl rfl rfl
  have h37 : BatchSpec 37 1000 1000 117628 1000 := BatchSpec.joinHeight1000 h36 RHHeight1000.em_main_0037_0037 rfl rfl rfl
  have h38 : BatchSpec 38 1000 1000 119766 1000 := BatchSpec.joinHeight1000 h37 RHHeight1000.em_main_0038_0038 rfl rfl rfl
  have h39 : BatchSpec 39 1000 1000 121891 1000 := BatchSpec.joinHeight1000 h38 RHHeight1000.em_main_0039_0039 rfl rfl rfl
  have h40 : BatchSpec 40 1000 1000 124004 1000 := BatchSpec.joinHeight1000 h39 RHHeight1000.em_main_0040_0040 rfl rfl rfl
  have h41 : BatchSpec 41 1000 1000 126105 1000 := BatchSpec.joinHeight1000 h40 RHHeight1000.em_main_0041_0041 rfl rfl rfl
  have h42 : BatchSpec 42 1000 1000 128194 1000 := BatchSpec.joinHeight1000 h41 RHHeight1000.em_main_0042_0042 rfl rfl rfl
  have h43 : BatchSpec 43 1000 1000 130272 1000 := BatchSpec.joinHeight1000 h42 RHHeight1000.em_main_0043_0043 rfl rfl rfl
  have h44 : BatchSpec 44 1000 1000 132339 1000 := BatchSpec.joinHeight1000 h43 RHHeight1000.em_main_0044_0044 rfl rfl rfl
  have h45 : BatchSpec 45 1000 1000 134395 1000 := BatchSpec.joinHeight1000 h44 RHHeight1000.em_main_0045_0045 rfl rfl rfl
  have h46 : BatchSpec 46 1000 1000 136442 1000 := BatchSpec.joinHeight1000 h45 RHHeight1000.em_main_0046_0046 rfl rfl rfl
  have h47 : BatchSpec 47 1000 1000 138478 1000 := BatchSpec.joinHeight1000 h46 RHHeight1000.em_main_0047_0047 rfl rfl rfl
  have h48 : BatchSpec 48 1000 1000 140505 1000 := BatchSpec.joinHeight1000 h47 RHHeight1000.em_main_0048_0048 rfl rfl rfl
  have h49 : BatchSpec 49 1000 1000 142522 1000 := BatchSpec.joinHeight1000 h48 RHHeight1000.em_main_0049_0049 rfl rfl rfl
  have h50 : BatchSpec 50 1000 1000 144530 1000 := BatchSpec.joinHeight1000 h49 RHHeight1000.em_main_0050_0050 rfl rfl rfl
  have h51 : BatchSpec 51 1000 1000 146530 1000 := BatchSpec.joinHeight1000 h50 RHHeight1000.em_main_0051_0051 rfl rfl rfl
  have h52 : BatchSpec 52 1000 1000 149500 1000 := BatchSpec.joinHeight1000 h51 RHHeight1000.em_main_0052_0052 rfl rfl rfl
  have h78 : BatchSpec 78 1000 1000 197830 1000 := BatchSpec.joinHeight1000 h52 RHHeight1000.rs_main_0001_0026 rfl rfl rfl
  have h88 : BatchSpec 88 1000 1000 215814 1000 := BatchSpec.joinHeight1000 h78 RHHeight1000.rs_main_0027_0036 rfl rfl rfl
  have h112 : BatchSpec 112 1000 1000 257388 1000 := BatchSpec.joinHeight1000 h88 RHHeight1000.rs_main_0037_0060 rfl rfl rfl
  have h130 : BatchSpec 130 1000 1000 287396 1000 := BatchSpec.joinHeight1000 h112 RHHeight1000.rs_main_0061_0078 rfl rfl rfl
  have h148 : BatchSpec 148 1000 1000 316604 1000 := BatchSpec.joinHeight1000 h130 RHHeight1000.rs_main_0079_0096 rfl rfl rfl
  have h166 : BatchSpec 166 1000 1000 345139 1000 := BatchSpec.joinHeight1000 h148 RHHeight1000.rs_main_0097_0114 rfl rfl rfl
  have h184 : BatchSpec 184 1000 1000 373095 1000 := BatchSpec.joinHeight1000 h166 RHHeight1000.rs_main_0115_0132 rfl rfl rfl
  have h202 : BatchSpec 202 1000 1000 400547 1000 := BatchSpec.joinHeight1000 h184 RHHeight1000.rs_main_0133_0150 rfl rfl rfl
  have h220 : BatchSpec 220 1000 1000 427552 1000 := BatchSpec.joinHeight1000 h202 RHHeight1000.rs_main_0151_0168 rfl rfl rfl
  have h238 : BatchSpec 238 1000 1000 454159 1000 := BatchSpec.joinHeight1000 h220 RHHeight1000.rs_main_0169_0186 rfl rfl rfl
  have h256 : BatchSpec 256 1000 1000 479682 1000 := BatchSpec.joinHeight1000 h238 RHHeight1000.rs_main_0187_0204 rfl rfl rfl
  have h274 : BatchSpec 274 1000 1000 506327 1000 := BatchSpec.joinHeight1000 h256 RHHeight1000.rs_main_0205_0222 rfl rfl rfl
  have h292 : BatchSpec 292 1000 1000 531948 1000 := BatchSpec.joinHeight1000 h274 RHHeight1000.rs_main_0223_0240 rfl rfl rfl
  have h304 : BatchSpec 304 1000 1000 548874 1000 := BatchSpec.joinHeight1000 h292 RHHeight1000.rs_main_0241_0252 rfl rfl rfl
  have h316 : BatchSpec 316 1000 1000 565685 1000 := BatchSpec.joinHeight1000 h304 RHHeight1000.rs_main_0253_0264 rfl rfl rfl
  have h328 : BatchSpec 328 1000 1000 582385 1000 := BatchSpec.joinHeight1000 h316 RHHeight1000.rs_main_0265_0276 rfl rfl rfl
  have h340 : BatchSpec 340 1000 1000 598981 1000 := BatchSpec.joinHeight1000 h328 RHHeight1000.rs_main_0277_0288 rfl rfl rfl
  have h352 : BatchSpec 352 1000 1000 615476 1000 := BatchSpec.joinHeight1000 h340 RHHeight1000.rs_main_0289_0300 rfl rfl rfl
  have h364 : BatchSpec 364 1000 1000 631875 1000 := BatchSpec.joinHeight1000 h352 RHHeight1000.rs_main_0301_0312 rfl rfl rfl
  have h376 : BatchSpec 376 1000 1000 648182 1000 := BatchSpec.joinHeight1000 h364 RHHeight1000.rs_main_0313_0324 rfl rfl rfl
  have h388 : BatchSpec 388 1000 1000 664401 1000 := BatchSpec.joinHeight1000 h376 RHHeight1000.rs_main_0325_0336 rfl rfl rfl
  have h400 : BatchSpec 400 1000 1000 681206 1000 := BatchSpec.joinHeight1000 h388 RHHeight1000.rs_main_0337_0348 rfl rfl rfl
  have h412 : BatchSpec 412 1000 1000 696589 1000 := BatchSpec.joinHeight1000 h400 RHHeight1000.rs_main_0349_0360 rfl rfl rfl
  have h424 : BatchSpec 424 1000 1000 712564 1000 := BatchSpec.joinHeight1000 h412 RHHeight1000.rs_main_0361_0372 rfl rfl rfl
  have h436 : BatchSpec 436 1000 1000 728464 1000 := BatchSpec.joinHeight1000 h424 RHHeight1000.rs_main_0373_0384 rfl rfl rfl
  have h448 : BatchSpec 448 1000 1000 744291 1000 := BatchSpec.joinHeight1000 h436 RHHeight1000.rs_main_0385_0396 rfl rfl rfl
  have h460 : BatchSpec 460 1000 1000 760048 1000 := BatchSpec.joinHeight1000 h448 RHHeight1000.rs_main_0397_0408 rfl rfl rfl
  have h472 : BatchSpec 472 1000 1000 775738 1000 := BatchSpec.joinHeight1000 h460 RHHeight1000.rs_main_0409_0420 rfl rfl rfl
  have h484 : BatchSpec 484 1000 1000 791361 1000 := BatchSpec.joinHeight1000 h472 RHHeight1000.rs_main_0421_0432 rfl rfl rfl
  have h490 : BatchSpec 490 1000 1000 799149 1000 := BatchSpec.joinHeight1000 h484 RHHeight1000.rs_main_0433_0438 rfl rfl rfl
  have h496 : BatchSpec 496 1000 1000 806921 1000 := BatchSpec.joinHeight1000 h490 RHHeight1000.rs_main_0439_0444 rfl rfl rfl
  have h502 : BatchSpec 502 1000 1000 814678 1000 := BatchSpec.joinHeight1000 h496 RHHeight1000.rs_main_0445_0450 rfl rfl rfl
  have h514 : BatchSpec 514 1000 1000 830146 1000 := BatchSpec.joinHeight1000 h502 RHHeight1000.rs_main_0451_0462 rfl rfl rfl
  have h526 : BatchSpec 526 1000 1000 845556 1000 := BatchSpec.joinHeight1000 h514 RHHeight1000.rs_main_0463_0474 rfl rfl rfl
  have h538 : BatchSpec 538 1000 1000 860908 1000 := BatchSpec.joinHeight1000 h526 RHHeight1000.rs_main_0475_0486 rfl rfl rfl
  have h550 : BatchSpec 550 1000 1000 876205 1000 := BatchSpec.joinHeight1000 h538 RHHeight1000.rs_main_0487_0498 rfl rfl rfl
  have h562 : BatchSpec 562 1000 1000 891448 1000 := BatchSpec.joinHeight1000 h550 RHHeight1000.rs_main_0499_0510 rfl rfl rfl
  have h574 : BatchSpec 574 1000 1000 906639 1000 := BatchSpec.joinHeight1000 h562 RHHeight1000.rs_main_0511_0522 rfl rfl rfl
  have h580 : BatchSpec 580 1000 1000 913584 1000 := BatchSpec.joinHeight1000 h574 RHHeight1000.rs_main_0523_0528 rfl rfl rfl
  have h592 : BatchSpec 592 1000 1000 929330 1000 := BatchSpec.joinHeight1000 h580 RHHeight1000.rs_main_0529_0540 rfl rfl rfl
  have h604 : BatchSpec 604 1000 1000 944396 1000 := BatchSpec.joinHeight1000 h592 RHHeight1000.rs_main_0541_0552 rfl rfl rfl
  have h616 : BatchSpec 616 1000 1000 959413 1000 := BatchSpec.joinHeight1000 h604 RHHeight1000.rs_main_0553_0564 rfl rfl rfl
  have h628 : BatchSpec 628 1000 1000 974151 1000 := BatchSpec.joinHeight1000 h616 RHHeight1000.rs_main_0565_0576 rfl rfl rfl
  have h640 : BatchSpec 640 1000 1000 989310 1000 := BatchSpec.joinHeight1000 h628 RHHeight1000.rs_main_0577_0588 rfl rfl rfl
  have h652 : BatchSpec 652 1000 1000 1004192 1000 := BatchSpec.joinHeight1000 h640 RHHeight1000.rs_main_0589_0600 rfl rfl rfl
  have h656 : BatchSpec 656 1000 1000 1008988 1000 := BatchSpec.joinHeight1000 h652 RHHeight1000.ordinary_batch4_inline_tail rfl rfl rfl
  exact RHHeight1000.close_from_656_intervals_and_gram RHHeight1000.certified_gram_sequence_655 h656 s hz h0 h1 hi
#print axioms solution
