-- Prove2me | solution 1 for ThreeSum.WeightedGlobalExecutableParameters.source_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:02:43.168685+00:00
-- url     : https://prove2.me/submissions/a7c2c782-5bb2-4b94-8028-b1e276fa37ca

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryExecutable
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
import Theorems.Thm_ThreeSum_WeightedGlobalNativeCoverWitness_source_records_nonempty


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalExecutableParameters
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverGoodMaps
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters WeightedGlobalNativeCoverWitness WeightedGlobalCoverScale
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalExecutableParameters
theorem _root_.solution {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k) (right : Bool) :
    0<(WeightedGlobalNativeCompleteFrontend.localRecords (maps K m k) (cap K m) right).length := by
  have hh := source_records_nonempty (maps K m k) (cap K m) (threshold K m k) (cover hK hm hk)
  cases right
  · exact hh.1
  · exact hh.2
end ThreeSum.WeightedGlobalExecutableParameters
