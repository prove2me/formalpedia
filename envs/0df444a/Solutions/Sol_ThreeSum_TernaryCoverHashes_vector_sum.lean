-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.vector_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:50.873143+00:00
-- url     : https://prove2.me/submissions/5fdde21c-e3dd-4a0e-a2a2-7c47a98b6a46

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
theorem _root_.solution {x y q : ι → K} (hsum : ∀ i, x i + y i = q i) :
    leftVector x + rightVector y = outputVector q := by
  funext i
  cases i with
  | inl i => exact hsum i
  | inr b => cases b <;> simp [leftVector, rightVector, outputVector]
end ThreeSum.TernaryCoverHashes
