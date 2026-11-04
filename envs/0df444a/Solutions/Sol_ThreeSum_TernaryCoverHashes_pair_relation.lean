-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.pair_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:51.871041+00:00
-- url     : https://prove2.me/submissions/bcda4b66-7928-4a7d-92f4-0d5e2968b6c5

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Tactic.LinearCombination
import Definitions.Def_Submission_ThreeSum_TernaryCoverHashes
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverHashes
open scoped BigOperators
variable {ι K : Type*} [Fintype ι] [Field K]
namespace ThreeSum.TernaryCoverHashes
theorem _root_.solution (x y : ι → K) {a b : K}
    (h : ∀ i, a * leftVector x i + b * rightVector y i = 0) :
    a = 0 ∧ b = 0 := by
  exact ⟨by simpa [leftVector, rightVector] using h (.inr false),
    by simpa [leftVector, rightVector] using h (.inr true)⟩
end ThreeSum.TernaryCoverHashes
