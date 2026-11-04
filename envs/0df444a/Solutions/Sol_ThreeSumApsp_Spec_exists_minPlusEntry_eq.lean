-- Prove2me | solution 1 for ThreeSumApsp.Spec.exists_minPlusEntry_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:16.581931+00:00
-- url     : https://prove2.me/submissions/ff957dc4-6b87-4ab8-8eb2-9603c4217262

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Theorems.Thm_List_exists_foldl_min_eq


set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) (A B : List ℤ) (i j : ℕ) :
    ∃ k < n, minPlusEntry n A B i j = entry n A i k + entry n B k j := by
  obtain ⟨k, hk, he⟩ :=
    List.exists_foldl_min_eq (fun k => entry n A i k + entry n B k j) (n - 1)
  exact ⟨k, by omega, he⟩
end ThreeSumApsp.Spec
