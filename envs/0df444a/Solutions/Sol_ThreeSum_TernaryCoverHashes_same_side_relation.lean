-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.same_side_relation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:53.195972+00:00
-- url     : https://prove2.me/submissions/0e20ebc8-16c4-4e7e-8627-a79f9516d6b3

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
theorem _root_.solution {x y : ι → K} (hxy : x ≠ y) (z : ι → K)
    {a b c : K}
    (h : ∀ i, a * leftVector x i + b * leftVector y i +
      c * rightVector z i = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  classical
  have hab : a + b = 0 := by
    simpa [leftVector, rightVector] using h (.inr false)
  have hc : c = 0 := by
    simpa [leftVector, rightVector] using h (.inr true)
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
    by_contra! hsame
    exact hxy (funext hsame)
  have he : a * (x i - y i) = 0 := by
    have hr : a * x i + b * y i + c * z i = 0 := h (.inl i)
    linear_combination hr - y i * hab - z i * hc
  have ha : a = 0 := (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hi)
  exact ⟨ha, by simpa [ha] using hab, hc⟩
end ThreeSum.TernaryCoverHashes
