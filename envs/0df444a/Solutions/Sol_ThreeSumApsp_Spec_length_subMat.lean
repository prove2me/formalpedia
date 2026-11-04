-- Prove2me | solution 1 for ThreeSumApsp.Spec.length_subMat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:04.639588+00:00
-- url     : https://prove2.me/submissions/4f8b3f18-d905-4455-943b-f1fce6ec74d9

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Theorems.Thm_ThreeSumApsp_Spec_length_affL
attribute [local simp] ThreeSumApsp.Spec.length_affL

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution (s h r0 c0 : ℕ) (L : List ℤ) :
    (subMat s h r0 c0 L).length = h * h := by
  simp [subMat]
end ThreeSumApsp.Spec
