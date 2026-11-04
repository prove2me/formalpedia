-- Prove2me | solution 1 for ThreeSum.LocalMaskHashes.left_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:10.461214+00:00
-- url     : https://prove2.me/submissions/1d2b82fa-9f52-4ffe-a1cf-cf2acf09c47d

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Theorems.Thm_ThreeSum_LocalMaskHashes_leftCode_lt
import Theorems.Thm_ThreeSum_LocalMaskHashes_leftCode_cast
import Definitions.Def_WeightedCache3SUM_Alias_0e1a7cfc44b05307
import Theorems.Thm_ThreeSum_LocalGraph_leftWord_injective


set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}
namespace ThreeSum.LocalMaskHashes
theorem _root_.solution (w : Weight L (LocalField h)) {r : ℕ} (hr : r < localPrime h) :
    LightHistogram.count (leftCode w k) r (LocalMaskGraph.vertexCount L k) =
      HashFamily.bucketSize (LocalGraph.leftVertices L k) w (r : LocalField h) :=
  indexed_bucket_count w LocalGraph.leftWord LocalGraph.leftWord_injective
    (leftCode w k) (fun i _ => leftCode_lt w k i) (fun _ hi => leftCode_cast w hi) hr
end ThreeSum.LocalMaskHashes
