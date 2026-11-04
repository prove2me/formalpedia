-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.hashes_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:55:09.111452+00:00
-- url     : https://prove2.me/submissions/bf7fd9a2-db7e-4e78-b80a-4f7612731abd

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverHashes_vector_sum
import Theorems.Thm_ThreeSum_TernaryJointType_fieldWord_sum
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
variable [Fact (Nat.Prime p)]
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution {α π : DigitType} (w : Coordinate (Fin L) → ZMod p)
    (e : LocalEdge L α π) : leftHash w e + rightHash w e = outputHash w (output e) := by
  have hv := vector_sum (fieldWord_sum (p := p) (edge_data e).2.2.2)
  unfold leftHash rightHash outputHash linearHash fieldLeft fieldRight
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have hi := congrFun hv i
  dsimp at hi
  rw [← hi, add_mul]
end ThreeSum.TernaryCoverLocal
