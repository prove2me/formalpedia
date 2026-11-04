-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.prime_word_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:54:38.491188+00:00
-- url     : https://prove2.me/submissions/529a95c0-2f2c-456d-bfc7-3a351de0e51d

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_count_le
import Theorems.Thm_ThreeSum_EncodedColorResources_normalized_word_bound
import Definitions.Def_WeightedCache3SUM_Alias_2dd23f958f4ab8ac
import Theorems.Thm_ThreeSum_ColorBandBounds_count_le
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_count_le
import Definitions.Def_WeightedCache3SUM_Alias_aa1db49eeb0333a7
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_LightBandRawAResources_count_le
import Theorems.Thm_ThreeSum_LightHistogram_count_le
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
theorem _root_.solution (n U : ℕ) : LightEncodedColorPrimeHost.inputWord n U ≤ 10000*(scale n)^6+9*U := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hg := (dimensions n).2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hy := (scale_bounds n).2.2.2.2.2
  have hR := count_le n
  have hnrm := normalized_word_bound n U
  have hcore := prime_core_word_bound n U
  have hp16 : scale n ≤ (scale n)^6 := Nat.le_self_pow (by decide) _
  have hp26 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 6)
  have hcountEq : LightEncodedColorPrime.count n n n (bandSize n)=ColorBandBounds.count n (bandSize n) := by
    unfold LightEncodedColorPrime.count ColorBandBounds.count
    ring
  have hprime : LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U ≤
      6000*(scale n)^6+4*U := by
    unfold LightEncodedColorPrime.word
    rw [hcountEq]
    nlinarith only [hb,hn,hR,hcore,hp16,hp26]
  have hmax : max (LightEncodedColorNormalize.word n U)
      (LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U) ≤
      9000*(scale n)^6+9*U := max_le (by nlinarith only [hnrm,hp26]) (by omega)
  unfold LightEncodedColorPrimeHost.inputWord
  nlinarith only [hb,hg,hM,hy,hmax,hp16]
end ThreeSum.EncodedColorResources
