-- Prove2me | solution 1 for ThreeSum.OriginalThreeSum.task_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:26:52.275667+00:00
-- url     : https://prove2.me/submissions/fa1e35dc-cd8d-4457-b79f-302758dc7a95

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum

set_option autoImplicit false
open ThreeSum ThreeSum.OriginalThreeSum
open Light ThreeSumApsp.Spec
namespace ThreeSum.OriginalThreeSum
theorem _root_.solution {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (H : x.Pre μ fr) :
    ∀ i : Fin x.N, μ (x.a+i.val)=vecOf x.N x.X i := by
  intro i
  exact H.seg.getD (by rw [H.len]; exact i.isLt) 0
end ThreeSum.OriginalThreeSum
