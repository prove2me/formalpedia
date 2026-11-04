-- Prove2me | solution 1 for ThreeSum.TernaryFrozenQueryStages.low_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:44:46.835069+00:00
-- url     : https://prove2.me/submissions/70255f74-9ba4-4a0b-9b00-8a6d09c963c3

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryFrozenQueryStages
theorem _root_.solution {N K : ℕ} (hK : K<N) :
    TernaryCodeSemantics.low (⟨K,hK⟩ : Fin N)=2*(N-(K+1)) := by
  unfold TernaryCodeSemantics.low
  change 2*(N-1-K)=2*(N-(K+1))
  congr 1
  omega
end ThreeSum.TernaryFrozenQueryStages
