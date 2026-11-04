-- Prove2me | solution 1 for ThreeSumApsp.Spec.entry_minPlusList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:40.514207+00:00
-- url     : https://prove2.me/submissions/d75de866-c51a-46d9-bc71-5ce2f2ce38b4

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
theorem _root_.solution {n : ℕ} (A B : List ℤ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    entry n (minPlusList n A B) i j = minPlusEntry n A B i j := by
  rw [entry, minPlusList, List.getD_map_range _ (Nat.mul_add_lt_mul hi hj),
    Nat.mul_add_div_of_lt hj,
    Nat.mul_add_mod_of_lt hj]
end ThreeSumApsp.Spec
