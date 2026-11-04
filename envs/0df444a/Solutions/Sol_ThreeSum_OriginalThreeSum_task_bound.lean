-- Prove2me | solution 1 for ThreeSum.OriginalThreeSum.task_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:26:53.502931+00:00
-- url     : https://prove2.me/submissions/b3ed8f64-2f8c-403c-8f53-361ddb2084ff

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
import Definitions.Def_Submission_ThreeSum_OriginalThreeSum
import Theorems.Thm_ThreeSumApsp_AbsLe_abs_getD_le


set_option autoImplicit false
open ThreeSum ThreeSum.OriginalThreeSum
open Light ThreeSumApsp.Spec
namespace ThreeSum.OriginalThreeSum
theorem _root_.solution {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (H : x.Pre μ fr) :
    ∀ i : Fin x.N, |vecOf x.N x.X i| ≤ (x.U : ℤ) := by
  intro i
  exact ThreeSumApsp.AbsLe.abs_getD_le (Int.natCast_nonneg _) H.le i.val
end ThreeSum.OriginalThreeSum
