-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.positionalHash_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:51.703969+00:00
-- url     : https://prove2.me/submissions/8905733b-1bbc-492e-b5be-1ba3ac458201

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_blockKey_choice
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
theorem _root_.solution (xs : List Ω) :
    Radix.positionalHash (p : ℤ) (rawRight maps occ edge) xs-
      Radix.positionalHash (p : ℤ) (rawLeft maps occ edge) xs =
    Radix.positionalHash (p : ℤ) (blockKey maps) (xs.map (blockOfChoice occ edge)) := by
  induction xs with
  | nil => simp [Radix.positionalHash]
  | cons c xs ih =>
    simp only [List.map_cons,Radix.positionalHash,blockKey_choice]
    rw [← ih]
    ring
end ThreeSum.TernaryGlobalEncoding
