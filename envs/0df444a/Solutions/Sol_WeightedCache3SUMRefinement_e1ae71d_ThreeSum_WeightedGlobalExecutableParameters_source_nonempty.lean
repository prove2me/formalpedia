-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExecutableParameters.source_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:00:51.710721+00:00
-- url     : https://prove2.me/submissions/e023b521-1511-4627-a6d4-6f875684b2a4

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExecutable
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativeCoverWitness
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernarySignedParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryExecutableParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalNativeCoverWitness_source_records_nonempty


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExecutableParameters
open WeightedGlobalOversizePrime WeightedGlobalOversizeOverhead WeightedGlobalCoverGoodMaps
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters WeightedGlobalNativeCoverWitness WeightedGlobalCoverScale
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExecutableParameters
theorem _root_.solution {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k) (right : Bool) :
    0<(WeightedGlobalNativeCompleteFrontend.localRecords (maps K m k) (cap K m) right).length := by
  have hh := source_records_nonempty (maps K m k) (cap K m) (threshold K m k) (cover hK hm hk)
  cases right
  · exact hh.1
  · exact hh.2
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalExecutableParameters
