-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.rawSource_cast_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:22.359898+00:00
-- url     : https://prove2.me/submissions/5588696b-1865-4ca5-9138-c27b62615831

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
    (rawSource w false (left e) : ZMod p) = leftHash w e := by
  simp [rawSource,leftHash,linearHash,leftVector,fieldLeft,fieldWord,Fintype.sum_sum_type,mul_comm,add_comm]
end ThreeSum.TernaryGlobalEncoding
