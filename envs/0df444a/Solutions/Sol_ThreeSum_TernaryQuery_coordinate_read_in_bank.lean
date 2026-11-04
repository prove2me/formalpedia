-- Prove2me | solution 1 for ThreeSum.TernaryQuery.coordinate_read_in_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:13.648238+00:00
-- url     : https://prove2.me/submissions/dbf3ddac-b4f2-4c1a-8468-bf0213eb5786

import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Theorems.Thm_ThreeSum_TernaryQuery_update_below
import Theorems.Thm_ThreeSum_TernaryBank_bank_downward_closed


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryQuery
open ThreeSum.TernaryJointType
open ThreeSum.TernaryBank
namespace ThreeSum.TernaryQuery
theorem _root_.solution {N T : ℕ} {R : TritWord N} (hR : R ∈ bank N T)
    (i : Fin N) (d : Fin 3) (hd : d ≤ R i) :
    Function.update R i d ∈ bank N T :=
  bank_downward_closed (update_below R i d hd) hR
end ThreeSum.TernaryQuery
