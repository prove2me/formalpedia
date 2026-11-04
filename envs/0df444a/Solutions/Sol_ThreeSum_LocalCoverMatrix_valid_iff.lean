-- Prove2me | solution 1 for ThreeSum.LocalCoverMatrix.valid_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:45.192107+00:00
-- url     : https://prove2.me/submissions/d2da9b68-106d-4f22-aa6e-bc3c6c13e79f

import Definitions.Def_Submission_ThreeSum_LocalMaskHashes
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LocalCoverMatrix
import Theorems.Thm_ThreeSum_LightTrimTest_flag_eq_one
import Theorems.Thm_ThreeSum_LocalMaskGraph_indexed_dot_zero_iff


set_option autoImplicit false
open ThreeSum ThreeSum.LocalCoverMatrix
open Finset LocalHashMoments LocalCoverBounds LocalMaskGraph LocalMaskHashes
variable {h L k : ℕ}
namespace ThreeSum.LocalCoverMatrix
theorem _root_.solution (w : Weight L (LocalField h)) {B i : ℕ}
    (hi : i < LocalMaskGraph.vertexCount L k*LocalMaskGraph.vertexCount L k) :
    valid w k B i=1 ↔
      Disjoint (setAt L k (i/LocalMaskGraph.vertexCount L k))
        (setAt L k (i%LocalMaskGraph.vertexCount L k)) ∧
      leftCount w k (leftCode w k (i/LocalMaskGraph.vertexCount L k)) ≤ B ∧
      rightCount w k (rightCode w k (i%LocalMaskGraph.vertexCount L k)) ≤ B := by
  have hn : 0 < LocalMaskGraph.vertexCount L k := by nlinarith
  have hq : i/LocalMaskGraph.vertexCount L k < LocalMaskGraph.vertexCount L k :=
    (Nat.div_lt_iff_lt_mul hn).mpr hi
  have hr := Nat.mod_lt i hn
  unfold valid LightPairFlags.pairFlag bits
  rw [LightTrimTest.flag_eq_one,indexed_dot_zero_iff hq hr]
end ThreeSum.LocalCoverMatrix
