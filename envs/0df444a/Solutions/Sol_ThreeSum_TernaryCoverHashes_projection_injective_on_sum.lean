-- Prove2me | solution 1 for ThreeSum.TernaryCoverHashes.projection_injective_on_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:37.11812+00:00
-- url     : https://prove2.me/submissions/5d77608b-0935-435a-b2a2-1e32fdf28cbb

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
theorem _root_.solution {a b x y x' y' : K} (hab : a ≠ b)
    (hsum : x + y = x' + y')
    (hprojection : a * x + b * y = a * x' + b * y') :
    x = x' ∧ y = y' := by
  have he : (a - b) * (x - x') = 0 := by
    linear_combination hprojection - b * hsum
  have hx : x = x' := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hab))
  exact ⟨hx, by simpa [hx] using hsum⟩
end ThreeSum.TernaryCoverHashes
