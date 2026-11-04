-- Prove2me | solution 1 for ThreeSum.LocalMaskHashes.leftCode_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:58.364285+00:00
-- url     : https://prove2.me/submissions/07b47e0b-07f3-4d8d-ab1a-8454dbef77b0

import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Definitions.Def_Submission_ThreeSum_LightHashHistogram
import Definitions.Def_Submission_ThreeSum_LightResidueHistogram
import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Theorems.Thm_ThreeSum_GlobalEncoding_rawHash_cast
import Theorems.Thm_ThreeSum_LightResidueHistogram_residue_zmod
import Theorems.Thm_ThreeSum_LocalCoverBounds_localPrime_pos
import Theorems.Thm_ThreeSum_LocalMaskGraph_subsetMask_setAt
import Theorems.Thm_ThreeSum_OneHotMask_eval_rawLeft


set_option autoImplicit false
open ThreeSum ThreeSum.LocalMaskHashes
open Finset LocalMaskGraph LocalHashMoments LocalCoverBounds
variable {h L k : ℕ}
namespace ThreeSum.LocalMaskHashes
theorem _root_.solution (w : Weight L (LocalField h)) {i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k) :
    (leftCode w k i : LocalField h) =
      HashFamily.hashValue w (LocalGraph.leftWord (setAt L k i)) := by
  unfold leftCode LightHashHistogram.code coeff
  rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
    ← subsetMask_setAt hi,OneHotMask.eval_rawLeft,GlobalEncoding.rawHash_cast]
end ThreeSum.LocalMaskHashes
