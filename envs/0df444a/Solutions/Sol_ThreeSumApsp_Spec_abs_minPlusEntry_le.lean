-- Prove2me | solution 1 for ThreeSumApsp.Spec.abs_minPlusEntry_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:39.311856+00:00
-- url     : https://prove2.me/submissions/6c191a82-44ee-4348-b8dc-3418f8678eea

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Theorems.Thm_ThreeSumApsp_Spec_exists_minPlusEntry_eq
import Theorems.Thm_ThreeSumApsp_AbsLe_abs_getD_le


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {A B : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hA : AbsLe A U) (hB : AbsLe B U) (i j : ℕ) : |minPlusEntry n A B i j| ≤ 2 * U := by
  obtain ⟨k, -, he⟩ := exists_minPlusEntry_eq hn A B i j
  have ha := AbsLe.abs_getD_le hU hA (i * n + k)
  have hb := AbsLe.abs_getD_le hU hB (k * n + j)
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)
end ThreeSumApsp.Spec
