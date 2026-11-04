-- Prove2me | solution 1 for ThreeSumApsp.Spec.length_minPlusList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:37.681848+00:00
-- url     : https://prove2.me/submissions/abbc4d1e-fe0f-482a-ab23-01adf7023042

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Theorems.Thm_ThreeSumApsp_Spec_length_affL
import Theorems.Thm_ThreeSumApsp_Spec_length_subMat
attribute [local simp] ThreeSumApsp.Spec.length_affL
attribute [local simp] ThreeSumApsp.Spec.length_subMat

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution (n : ℕ) (A B : List ℤ) : (minPlusList n A B).length = n * n := by
  simp [minPlusList]
end ThreeSumApsp.Spec
