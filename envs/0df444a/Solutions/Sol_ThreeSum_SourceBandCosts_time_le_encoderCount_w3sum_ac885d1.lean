-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.time_le_encoderCount_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:14:52.497741+00:00
-- url     : https://prove2.me/submissions/798bfb89-1b16-435d-ac61-dfb3fa760745

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_input_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_bands_modulus_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_bands_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_size_le_bandCount
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_LightBlockCoefficients_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_62675b0b68a02f51
import Definitions.Def_WeightedCache3SUM_Alias_8e086529b85f69a3
import Theorems.Thm_ThreeSum_LightBlockSourceHashes_time_bound
import Theorems.Thm_ThreeSum_LightBlockSourceRetainedProgram_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_395153661a990775
import Theorems.Thm_ThreeSum_LightBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightCanonicalBoxSum_time_bound
import Theorems.Thm_ThreeSum_LightDownsetAddress_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_432686f9c1a6224e
import Definitions.Def_WeightedCache3SUM_Alias_f1b1ba0c94539568
import Theorems.Thm_ThreeSum_LightDownsetSize_time_bound
import Theorems.Thm_ThreeSum_LightExplicitSum_time_bound
import Theorems.Thm_ThreeSum_LightLeafSum_time_bound
import Theorems.Thm_ThreeSum_LightLocalCoverRow_time_bound
import Theorems.Thm_ThreeSum_LightMaskBits_time_bound
import Theorems.Thm_ThreeSum_LightMaskHashes_time_bound
import Theorems.Thm_ThreeSum_LightMaskMinimum_time_bound
import Theorems.Thm_ThreeSum_LightMaskUnion_time_bound
import Theorems.Thm_ThreeSum_LightPairFlags_time_bound
import Theorems.Thm_ThreeSum_LightQueryBox_time_bound
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixBatch_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixCell_time_bound
import Theorems.Thm_ThreeSum_LightReportingSuffixSetup_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_306830be6786141e
import Theorems.Thm_ThreeSum_LightResidueHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSignedBoxSetup_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafBatch_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafCell_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafGeneral_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeafTable_time_bound
import Theorems.Thm_ThreeSum_LightSignedLeaf_time_bound
import Theorems.Thm_ThreeSum_LightSmallDivide_time_bound
import Theorems.Thm_ThreeSum_LightSourceBandBatch_time_bound
import Theorems.Thm_ThreeSum_LightSourceBandSetup_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketFromHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceBucketOriginal_time_bound
import Theorems.Thm_ThreeSum_LightSourceBuild_time_bound
import Theorems.Thm_ThreeSum_LightSourceFlagArray_time_bound
import Theorems.Thm_ThreeSum_LightSourceGather_time_bound
import Theorems.Thm_ThreeSum_LightSourceHistogram_time_bound
import Theorems.Thm_ThreeSum_LightSourceMaskFlags_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_5747fe39e5f06311
import Theorems.Thm_ThreeSum_LightSourcePreparation_time_bound
import Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
import Theorems.Thm_ThreeSum_LightSourceRetainedStages_time_bound
import Theorems.Thm_ThreeSum_LightSourceRowFlag_time_bound
import Theorems.Thm_ThreeSum_LightSourceStages_time_bound
import Theorems.Thm_ThreeSum_LightSourceTrim_time_bound
import Theorems.Thm_ThreeSum_LightSparseQuery_time_bound
import Theorems.Thm_ThreeSum_LightStageLookup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumerationSetup_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightSubsetSetup_time_bound
import Theorems.Thm_ThreeSum_LightWeightDecode_time_bound
import Theorems.Thm_ThreeSum_LightZetaBatch_time_bound
import Theorems.Thm_ThreeSum_LightZetaCell_time_bound
import Definitions.Def_WeightedCache3SUM_Alias_223d9caf4e7f660b
import Definitions.Def_WeightedCache3SUM_Alias_c2a1891cab57c5b2


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution {N n p U D : ℕ} (hN : N ≤ n) :
    LightSourceBandSetup.time N (bandSize n) p
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) U D ≤
      (1016*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+1946)*encoderCount n+560 := by
  have ht := LightSourceBandSetup.time_bound N (bandSize n) p
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) U D (bandSize_pos n)
  have hn := hN.trans (input_le_encoderCount n)
  have hb := size_le_bandCount hN
  have hm := (Nat.mul_le_mul_right
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) hb).trans
      (bands_modulus_le_encoderCount n)
  have hbc := hb.trans (bands_le_encoderCount n)
  have hscan := Nat.mul_le_mul_left 1016 (Nat.mul_le_mul_right
    (Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1) hn)
  nlinarith
end ThreeSum.SourceBandCosts
