-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.rawOutput_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:38.379449+00:00
-- url     : https://prove2.me/submissions/80f66bde-cb1d-4296-b4f0-61b2aa2af1d7

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
theorem _root_.solution (w : Coordinate (Fin L) → ZMod p) (q : TritWord L) :
    0 ≤ rawOutput w q := by
  unfold rawOutput
  exact add_nonneg (add_nonneg (by positivity) (by positivity))
    (sum_nonneg (fun i _ => by positivity))
end ThreeSum.TernaryGlobalEncoding
