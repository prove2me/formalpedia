-- Prove2me | solution 1 for ThreeSum.WeightedGlobalExecutableParameters.output_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:59:39.020912+00:00
-- url     : https://prove2.me/submissions/f741370e-fe64-4774-9935-9cbbda582fe2

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryExecutable
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalExecutableParameters
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverGoodMaps
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters WeightedGlobalNativeCoverWitness WeightedGlobalCoverScale
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalExecutableParameters
theorem _root_.solution {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k) :
    0<(WeightedGlobalGoodOutputCatalog.records (maps K m k) (threshold K m k)).length :=
  Classical.choose_spec (exists_output hK hm hk)
end ThreeSum.WeightedGlobalExecutableParameters
