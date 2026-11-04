-- Prove2me | solution 1 for ThreeSumApsp.Spec.entry_subMat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:35.336051+00:00
-- url     : https://prove2.me/submissions/ae5861e6-17aa-407b-9105-eb9143f76eb0

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Theorems.Thm_List_getD_map_range
import Theorems.Thm_Nat_mul_add_div_of_lt
import Theorems.Thm_Nat_mul_add_lt_mul


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution {s h r0 c0 : ℕ} {L : List ℤ} {i j : ℕ} (hi : i < h) (hj : j < h) :
    entry h (subMat s h r0 c0 L) i j = entry s L (r0 + i) (c0 + j) := by
  rw [entry, subMat, List.getD_map_range _ (Nat.mul_add_lt_mul hi hj), Nat.mul_add_div_of_lt hj,
    Nat.mul_add_mod_of_lt hj]
end ThreeSumApsp.Spec
