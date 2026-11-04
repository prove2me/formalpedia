-- Prove2me | solution 1 for ThreeSum.OriginalThreeSum.task_post
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:35.21858+00:00
-- url     : https://prove2.me/submissions/d6b6f738-f7e2-4218-913c-fd8ecebb2602

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Theorems.Thm_ThreeSum_OriginalThreeSum_flag_of_decision

set_option autoImplicit false
open ThreeSum ThreeSum.OriginalThreeSum
open Light ThreeSumApsp.Spec
namespace ThreeSum.OriginalThreeSum
theorem _root_.solution {x : VecInst} {μ ν : ℕ → ℤ} {fr : ℕ} {r : ℤ}
    (hbool : r=0 ∨ r=1) (hcorrect : r=1 ↔ Coloring.DistinctZeroSum (vecOf x.N x.X))
    (hkeep : Kept μ ν fr) : s3Task.Post x μ fr r ν :=
  ⟨flag_of_decision _ hbool hcorrect,hkeep⟩
end ThreeSum.OriginalThreeSum
