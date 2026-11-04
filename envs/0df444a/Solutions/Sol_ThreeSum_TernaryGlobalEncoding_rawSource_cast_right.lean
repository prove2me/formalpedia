-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.rawSource_cast_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:23.487504+00:00
-- url     : https://prove2.me/submissions/da1d6e57-9a87-41d5-b94d-f92b5554a673

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryGlobalEncoding
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]
variable (maps : I → Coordinate (Fin L) → ZMod p) (occ : Ω → I)
  (edge : Ω → LocalEdge L α π)
namespace ThreeSum.TernaryGlobalEncoding
theorem _root_.solution (w : Coordinate (Fin L) → ZMod p) (e : LocalEdge L α π) :
    (rawSource w true (right e) : ZMod p) = rightHash w e := by
  simp [rawSource,rightHash,linearHash,rightVector,fieldRight,fieldWord,Fintype.sum_sum_type,mul_comm,add_comm]
end ThreeSum.TernaryGlobalEncoding
