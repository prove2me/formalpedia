-- Prove2me | solution 1 for ThreeSum.TernaryFrozenQueryStages.high_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:48:06.021202+00:00
-- url     : https://prove2.me/submissions/d1685f70-766c-4945-8865-8be003b565a0

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryStages
import Theorems.Thm_ThreeSum_TernaryFrozenQueryStages_low_step
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryJointType ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryFrozenQueryStages
theorem _root_.solution {N K : ℕ} (hK : K<N) :
    TernaryCodeSemantics.high (⟨K,hK⟩ : Fin N)=2*(N-(K+1))+1 := by
  rw [TernaryCodeSemantics.high,low_step hK]
end ThreeSum.TernaryFrozenQueryStages
