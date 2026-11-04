-- Prove2me | solution 1 for ThreeSumApsp.Spec.abs_le_of_mem_subMat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:36.482426+00:00
-- url     : https://prove2.me/submissions/c9970518-34c9-455b-a8a7-d447b7316a05

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Theorems.Thm_ThreeSumApsp_AbsLe_abs_getD_le


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution {s h r0 c0 : ℕ} {L : List ℤ} {U : ℤ} (hU : 0 ≤ U) (hL : AbsLe L U) :
    AbsLe (subMat s h r0 c0 L) U :=
  List.forall_mem_map.2 fun _ _ => AbsLe.abs_getD_le hU hL _
end ThreeSumApsp.Spec
