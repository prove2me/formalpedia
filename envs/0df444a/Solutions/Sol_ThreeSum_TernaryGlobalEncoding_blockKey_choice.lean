-- Prove2me | solution 1 for ThreeSum.TernaryGlobalEncoding.blockKey_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:15:59.666641+00:00
-- url     : https://prove2.me/submissions/ffae5e7f-d1c1-44fe-bba0-d23c03c09f46

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Theorems.Thm_ThreeSum_TernaryGlobalEncoding_raw_addition
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
theorem _root_.solution (c : Ω) :
    blockKey maps (blockOfChoice occ edge c) = rawRight maps occ edge c-rawLeft maps occ edge c := by
  dsimp [blockKey,blockOfChoice,rawRight,rawLeft]
  linarith [raw_addition (maps (occ c)) (edge c)]
end ThreeSum.TernaryGlobalEncoding
