-- Prove2me | solution 1 for ThreeSum.LightExtensionMenuMatrix.cell_word_affine_ctx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:42.736696+00:00
-- url     : https://prove2.me/submissions/f766eb8b-8501-4fe4-9308-fcc2cab16179

import Definitions.Def_Submission_ThreeSum_LightExtensionMenuMatrix
import Definitions.Def_Submission_ThreeSum_LightExtensionMenuBudget

set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionMenuMatrix
set_option maxHeartbeats 3000000
namespace ThreeSum.LightExtensionMenuMatrix
theorem _root_.solution (C : LightExtensionQuotientPredicate.Layout) (q ctx : ℕ) :
    LightExtensionMultiplyCell.word C q ctx=ctx+LightExtensionMultiplyCell.word C q 0 := by
  unfold LightExtensionMultiplyCell.word
  omega
end ThreeSum.LightExtensionMenuMatrix
