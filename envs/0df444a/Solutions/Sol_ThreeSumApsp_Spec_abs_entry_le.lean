-- Prove2me | solution 1 for ThreeSumApsp.Spec.abs_entry_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:57.109527+00:00
-- url     : https://prove2.me/submissions/34a1db96-86ee-4e98-af7a-57bd11add0f8

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Theorems.Thm_ThreeSumApsp_AbsLe_abs_getD_le


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution (n : ℕ) {L : List ℤ} {U : ℤ} (hU : 0 ≤ U) (hL : AbsLe L U) (i j : ℕ) :
    |entry n L i j| ≤ U :=
  AbsLe.abs_getD_le hU hL _
end ThreeSumApsp.Spec
