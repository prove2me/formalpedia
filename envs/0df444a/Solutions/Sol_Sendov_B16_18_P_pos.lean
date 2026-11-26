-- Prove2me | solution 1 for Sendov.B16_18.P_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:24:47.225835+00:00
-- url     : https://prove2.me/submissions/60d358ad-25d5-4130-84e4-7c3839513bdc

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18

set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18
set_option maxHeartbeats 2000000
namespace Sendov.B16_18
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 17 / 2) :
    0 < 308547940078125 + 716274580556250 * α + 701075142421875 * α ^ 2 + 366034929547500 * α ^ 3 + 98713082723625 * α ^ 4 - 785317395690 * α ^ 5 - 34202916258669 * α ^ 6 + 6366700041480 * α ^ 7 + 121732471512 * α ^ 8 - 9494954208 * α ^ 9 - 1551607200 * α ^ 10 - 87661568 * α ^ 11 - 2586240 * α ^ 12 - 39936 * α ^ 13 - 256 * α ^ 14 := by
  have hu : (0 : ℝ) ≤ 17 - 2 * α := by linarith
  have h0 : (0:ℝ) ≤ 308547940078125 * (17 - 2 * α) ^ 14 :=
    mul_nonneg (by norm_num) (pow_nonneg hu 14)
  have h1 : (0:ℝ) ≤ 20816010191643750 * α ^ 1 * (17 - 2 * α) ^ 13 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 1)) (pow_nonneg hu 13)
  have h2 : (0:ℝ) ≤ 631515530954221875 * α ^ 2 * (17 - 2 * α) ^ 12 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 2)) (pow_nonneg hu 12)
  have h3 : (0:ℝ) ≤ 11358598773482842500 * α ^ 3 * (17 - 2 * α) ^ 11 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 3)) (pow_nonneg hu 11)
  have h4 : (0:ℝ) ≤ 134099015737057493625 * α ^ 4 * (17 - 2 * α) ^ 10 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 4)) (pow_nonneg hu 10)
  have h5 : (0:ℝ) ≤ 1075072539293623306170 * α ^ 5 * (17 - 2 * α) ^ 9 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 5)) (pow_nonneg hu 9)
  have h6 : (0:ℝ) ≤ 5177641117293101872899 * α ^ 6 * (17 - 2 * α) ^ 8 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 6)) (pow_nonneg hu 8)
  have h7 : (0:ℝ) ≤ 13260545037504883513944 * α ^ 7 * (17 - 2 * α) ^ 7 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 7)) (pow_nonneg hu 7)
  have h8 : (0:ℝ) ≤ 13392270163441462237560 * α ^ 8 * (17 - 2 * α) ^ 6 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 8)) (pow_nonneg hu 6)
  have h9 : (0:ℝ) ≤ 934363054464939802080 * α ^ 9 * (17 - 2 * α) ^ 5 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 9)) (pow_nonneg hu 5)
  have h10 : (0:ℝ) ≤ 56141276222621229749280 * α ^ 10 * (17 - 2 * α) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 10)) (pow_nonneg hu 4)
  have h11 : (0:ℝ) ≤ 269593608305522330908544 * α ^ 11 * (17 - 2 * α) ^ 3 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 11)) (pow_nonneg hu 3)
  have h12 : (0:ℝ) ≤ 451523429099140347738624 * α ^ 12 * (17 - 2 * α) ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 12)) (pow_nonneg hu 2)
  have h13 : (0:ℝ) ≤ 320966535936278232000000 * α ^ 13 * (17 - 2 * α) ^ 1 :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hα 13)) (pow_nonneg hu 1)
  have h14 : (0:ℝ) ≤ 72913603873782672000000 * α ^ 14 :=
    mul_nonneg (by norm_num) (pow_nonneg hα 14)
  have hid : (17 : ℝ) ^ 14 * (308547940078125 + 716274580556250 * α + 701075142421875 * α ^ 2 + 366034929547500 * α ^ 3 + 98713082723625 * α ^ 4 - 785317395690 * α ^ 5 - 34202916258669 * α ^ 6 + 6366700041480 * α ^ 7 + 121732471512 * α ^ 8 - 9494954208 * α ^ 9 - 1551607200 * α ^ 10 - 87661568 * α ^ 11 - 2586240 * α ^ 12 - 39936 * α ^ 13 - 256 * α ^ 14) = 308547940078125 * (17 - 2 * α) ^ 14 + 20816010191643750 * α ^ 1 * (17 - 2 * α) ^ 13 + 631515530954221875 * α ^ 2 * (17 - 2 * α) ^ 12 + 11358598773482842500 * α ^ 3 * (17 - 2 * α) ^ 11 + 134099015737057493625 * α ^ 4 * (17 - 2 * α) ^ 10 + 1075072539293623306170 * α ^ 5 * (17 - 2 * α) ^ 9 + 5177641117293101872899 * α ^ 6 * (17 - 2 * α) ^ 8 + 13260545037504883513944 * α ^ 7 * (17 - 2 * α) ^ 7 + 13392270163441462237560 * α ^ 8 * (17 - 2 * α) ^ 6 + 934363054464939802080 * α ^ 9 * (17 - 2 * α) ^ 5 + 56141276222621229749280 * α ^ 10 * (17 - 2 * α) ^ 4 + 269593608305522330908544 * α ^ 11 * (17 - 2 * α) ^ 3 + 451523429099140347738624 * α ^ 12 * (17 - 2 * α) ^ 2 + 320966535936278232000000 * α ^ 13 * (17 - 2 * α) ^ 1 + 72913603873782672000000 * α ^ 14 := by
    ring
  rcases le_total α (17 / (2 * 2)) with h | h
  · have hpos : (0 : ℝ) < 308547940078125 * (17 - 2 * α) ^ 14 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 14)
    linarith
  · have hpos : (0 : ℝ) < 72913603873782672000000 * α ^ 14 :=
      mul_pos (by norm_num) (pow_pos (by linarith) 14)
    linarith
end Sendov.B16_18
