-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExecutableParameters.output_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:05:21.721714+00:00
-- url     : https://prove2.me/submissions/477bda04-f1e3-4d67-b0e3-6cb14a64cf92

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExecutable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExecutableParameters

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExecutableParameters
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverGoodMaps
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters WeightedGlobalNativeCoverWitness WeightedGlobalCoverScale
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExecutableParameters
theorem _root_.solution {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k) :
    0<(WeightedGlobalGoodOutputCatalog.records (maps K m k) (threshold K m k)).length :=
  Classical.choose_spec (exists_output hK hm hk)
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExecutableParameters
