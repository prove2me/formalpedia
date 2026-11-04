-- Prove2me | solution 1 for ThreeSum.LocalMaskHashes.right_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:11.862477+00:00
-- url     : https://prove2.me/submissions/6a7c1605-241a-44c4-8e5a-6a156c08fb03

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Theorems.Thm_ThreeSum_LocalMaskHashes_rightCode_lt
import Theorems.Thm_ThreeSum_LocalMaskHashes_rightCode_cast
import Definitions.Def_WeightedCache3SUM_Alias_0e1a7cfc44b05307
import Theorems.Thm_ThreeSum_LocalGraph_rightWord_injective


set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}
namespace ThreeSum.LocalMaskHashes
theorem _root_.solution (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (rightCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.rightVertices L k) w (r : LocalField h) :=
  indexed_bucket_count w LocalGraph.rightWord LocalGraph.rightWord_injective
    (rightCode w k) (fun i _ => rightCode_lt w k i) (fun _ hi => rightCode_cast w hi) hr
end ThreeSum.LocalMaskHashes
