-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.rawLeft_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:41:54.880208+00:00
-- url     : https://prove2.me/submissions/587fb8a8-6125-429d-9960-1be342d29fae

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawSource_nonnegative
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_rawSource_upper

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
theorem _root_.solution (c : Ω) :
    |rawLeft maps occ edge c| ≤ ((2*L+1)*p : ℕ) := by
  unfold rawLeft
  rw [abs_neg,abs_of_nonneg (rawSource_nonnegative _ _ _)]
  exact rawSource_upper _ _ _
end ThreeSum.TernaryGlobalEncoding
