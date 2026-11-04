-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.prime_core_word_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:28:44.945415+00:00
-- url     : https://prove2.me/submissions/6ac63638-4b66-46cd-a2bb-b72e97a07aa1

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_count_le
import Theorems.Thm_ThreeSum_EncodedColorResources_capacity_bound
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_ColorBandBounds_count_le
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_count_le
import Definitions.Def_WeightedCache3SUM_Alias_aa1db49eeb0333a7
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_LightBandRawAResources_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightPrimePool_size_le
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_count_le


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n U : ℕ) :
    LightEncodedColorPrimeCore.word (maxMod n) n n n (bandSize n)
      (ColorBandBounds.count n (bandSize n)) (radix n) (primeWindow n) U ≤ 5000*(scale n)^6+4*U := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hg := (dimensions n).2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hP := (scale_bounds n).2.2.2.2.1
  have hy := (scale_bounds n).2.2.2.2.2
  have hR := count_le n
  have hs := (LightPrimePool.size_le (primeWindow n)).trans (Nat.mul_le_mul_left 3 hy)
  have hcap := capacity_bound n
  have hg2 : bandSize n+1 ≤ 2*scale n := by omega
  have hkar : LightKaratsuba.wordBound (capacity (maxMod n)) (bandSize n) ≤ 4096*(scale n)^5 := by
    unfold LightKaratsuba.wordBound
    calc
      _ ≤ 128*(2*scale n)^3*(2*scale n)^2 := by gcongr
      _ = _ := by ring
  have hg3 := Nat.pow_le_pow_left hg 3
  have hsg := Nat.mul_le_mul (show LightPrimePool.size (primeWindow n)+1 ≤ 3*scale n+1 by omega) hg3
  have hrg := Nat.mul_le_mul hR (Nat.mul_le_mul hs hg3)
  have hdprod := Nat.mul_le_mul hy (Nat.add_le_add_right hM 4)
  have hp16 : scale n ≤ (scale n)^6 := Nat.le_self_pow (by decide) _
  have hp26 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 6)
  have hp36 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 6)
  have hp46 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 4 ≤ 6)
  have hp56 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 5 ≤ 6)
  have hweighted : LightBandWeightedScore.word (maxMod n) n n n (bandSize n)
      (ColorBandBounds.count n (bandSize n)) (LightPrimePool.size (primeWindow n)) U ≤ 5000*(scale n)^6+4*U := by
    unfold LightBandWeightedScore.word LightBandWeightedScoreCell.word LightWeightedScore.word LightModuloCounts.word
    nlinarith only [hb,hn,hg,hP,hR,hkar,hg3,hsg,hrg,hp16,hp26,hp36,hp46,hp56]
  unfold LightEncodedColorPrimeCore.word
  apply max_le
  · unfold LightBandPrimeDepth.word
    nlinarith only [hb,hM,hdprod,hp16,hp26]
  · apply max_le
    · unfold LightPrimePool.word
      nlinarith only [hb,hy,hp16]
    · exact hweighted
end ThreeSum.EncodedColorResources
