-- Prove2me | solution 1 for ThreeSum.BlockSourceCatalogCosts.work_le_encoderCount_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:14:51.21629+00:00
-- url     : https://prove2.me/submissions/8ea61bc0-d6ee-4e8b-bd67-e00c7d3126d6

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_count_eq_scheduleCount
import Theorems.Thm_ThreeSum_BlockSourceSharing_downset_add_one_le_fullOutputs
import Theorems.Thm_ThreeSum_BlockSourceSharing_width_eq
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
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout
namespace ThreeSum.BlockSourceCatalogCosts
theorem _root_.solution (n : ℕ) :
    work n ≤ LightBlockSourceCatalogProgram.factor
      (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)*encoderCount n := by
  have hcut : mu n ≤ blockCount (inputBits n)*(512*microHalf (inputBits n)) := by
    rw [width_eq]
    omega
  have ht := LightBlockSourceCatalogProgram.time_bound hcut
  rw [width_eq] at ht
  have hcpos : 0 < LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) :=
    pow_pos (OutputDecodeRecords.schedule_pos (microHalf (inputBits n))) _
  have hc : LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))+1 ≤
      2*LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) := by omega
  have hd := downset_add_one_le_fullOutputs n
  unfold work
  calc
    _ ≤ bandCount n*((LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))+1)*
        LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*
        (downsetCap (256*mu n) (mu n)+1)) := Nat.mul_le_mul_left _ ht
    _ ≤ bandCount n*((2*LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))*
        LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*
        ((256*mu n+2)*fullOutputs n)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) hd)
    _ = _ := by rw [count_eq_scheduleCount]; unfold encoderCount; ring
end ThreeSum.BlockSourceCatalogCosts
