-- Prove2me | solution 1 for ThreeSumApsp.Spec.triOf_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:58.335195+00:00
-- url     : https://prove2.me/submissions/b03d68e2-d811-4c4f-920e-61bca6239b2d

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Theorems.Thm_ThreeSumApsp_AbsLe_abs_getD_le


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution {n U : ℕ} {AB BC AC : List ℤ} (hAB : AbsLe AB U) (hBC : AbsLe BC U)
    (hAC : AbsLe AC U) : (triOf n AB BC AC).WeightsBoundedBy (U : ℤ) :=
  ⟨fun _ _ => AbsLe.abs_getD_le (Int.natCast_nonneg U) hAB _,
    fun _ _ => AbsLe.abs_getD_le (Int.natCast_nonneg U) hBC _,
    fun _ _ => AbsLe.abs_getD_le (Int.natCast_nonneg U) hAC _⟩
end ThreeSumApsp.Spec
