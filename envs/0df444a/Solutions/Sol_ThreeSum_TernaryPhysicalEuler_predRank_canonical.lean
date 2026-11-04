-- Prove2me | solution 1 for ThreeSum.TernaryPhysicalEuler.predRank_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:53:23.933361+00:00
-- url     : https://prove2.me/submissions/5954ddf1-179f-4437-809d-00d19a0bc95e

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMetadata
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Definitions.Def_Submission_ThreeSum_TernaryPartialEuler
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalEuler
import Theorems.Thm_ThreeSum_LightTernaryPredecessor_code_canonical
import Theorems.Thm_ThreeSum_LightTernaryRank_partialRank_address
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPhysicalEuler
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryPhysicalEuler
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) (hi : 0<(R i).val) :
    LightTernaryPredecessor.predRank N (LightTernaryEulerMetadata.lowAt N i.val)
      (LightTernaryEulerMetadata.highAt N i.val) (address R)=rank (predecessor R i) := by
  unfold LightTernaryPredecessor.predRank
  change LightTernaryRank.partialRank N
    (LightTernaryPredecessor.code N (low i) (high i) (address R)) N=rank (predecessor R i)
  rw [LightTernaryPredecessor.code_canonical R i hi,LightTernaryRank.partialRank_address]
end ThreeSum.TernaryPhysicalEuler
