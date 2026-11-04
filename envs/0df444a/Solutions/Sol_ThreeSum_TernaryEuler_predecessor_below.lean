-- Prove2me | solution 1 for ThreeSum.TernaryEuler.predecessor_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:16.070623+00:00
-- url     : https://prove2.me/submissions/0a9afcdb-de21-4d1c-8c4e-a9174145609f

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Theorems.Thm_ThreeSum_TernaryQuery_update_below


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank
namespace ThreeSum.TernaryEuler
theorem _root_.solution {N : ℕ} (R : TritWord N) (i : Fin N) :
    Below (predecessor R i) R := by
  apply ThreeSum.TernaryQuery.update_below
  change (R i).val - 1 ≤ (R i).val
  omega
end ThreeSum.TernaryEuler
