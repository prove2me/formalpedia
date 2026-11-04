-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.rawSource_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:53.259392+00:00
-- url     : https://prove2.me/submissions/8e5c53f6-e7fc-4034-a27d-7f514352999c

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding

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
theorem _root_.solution (w : Coordinate (Fin L) → ZMod p) (tag : Bool) (a : TritWord L) :
    0 ≤ rawSource w tag a := by
  unfold rawSource
  exact add_nonneg (by positivity) (sum_nonneg (fun i _ => by positivity))
end ThreeSum.TernaryGlobalEncoding
