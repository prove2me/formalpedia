-- Prove2me | solution 1 for ThreeSumApsp.Spec.minPlusEntry_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:58:38.149557+00:00
-- url     : https://prove2.me/submissions/7537cf7a-019d-49f5-81fa-f965d0e561e1

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Theorems.Thm_List_foldl_min_le


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution (n : ℕ) (A B : List ℤ) (i j : ℕ) {k : ℕ} (hk : k < n) :
    minPlusEntry n A B i j ≤ entry n A i k + entry n B k j :=
  List.foldl_min_le (fun k => entry n A i k + entry n B k j) (n - 1) (by omega)
end ThreeSumApsp.Spec
