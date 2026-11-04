-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.vectorPoly_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:55.243202+00:00
-- url     : https://prove2.me/submissions/c468789a-e3ed-4ad4-85a3-2409ef742626

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalRowMenu
open Finset
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]
namespace ThreeSum.TernaryOriginalRowMenu
theorem _root_.solution (Λ : ℕ) (v : Fin Λ → K) :
    (vectorPoly (E := E) Λ v).natDegree ≤ Λ - 1 := by
  by_cases h : Λ = 0
  · subst Λ
    simp [vectorPoly]
  · have hh := Polynomial.ofFn_natDegree_lt (R := E) (by omega : 1 ≤ Λ)
      (fun i => algebraMap K E (v i))
    exact Nat.le_pred_of_lt hh
end ThreeSum.TernaryOriginalRowMenu
