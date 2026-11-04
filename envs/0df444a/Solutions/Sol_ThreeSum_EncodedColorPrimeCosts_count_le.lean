-- Prove2me | solution 1 for ThreeSum.EncodedColorPrimeCosts.count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:23:50.372243+00:00
-- url     : https://prove2.me/submissions/49a9a152-a40f-4a12-a3a7-1907cd91a3d2

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_size_le_bandCount


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds
namespace ThreeSum.EncodedColorPrimeCosts
theorem _root_.solution {nA nB nC n : ℕ} (ha : nA ≤ n) (hb : nB ≤ n) (hc : nC ≤ n) :
    LightEncodedColorPrime.count nA nB nC (bandSize n) ≤ 3*bandCount n^2 := by
  have a := SourceBandCosts.size_le_bandCount ha
  have b := SourceBandCosts.size_le_bandCount hb
  have c := SourceBandCosts.size_le_bandCount hc
  have ab := Nat.mul_le_mul a b
  have ac := Nat.mul_le_mul a c
  have bc := Nat.mul_le_mul b c
  unfold LightEncodedColorPrime.count
  nlinarith
end ThreeSum.EncodedColorPrimeCosts
