-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.row_eq_dot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:59.457122+00:00
-- url     : https://prove2.me/submissions/514a56d0-5fbc-4366-a7dc-490dd83fe96e

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
theorem _root_.solution (Λ : ℕ) (ℓ : E →ₗ[K] K) (seed : E × E) (v : Fin Λ → K) :
    row Λ ℓ seed v = ∑ i, v i * seedRow Λ ℓ seed i := by
  have he : v = ∑ i, v i • Pi.single i 1 := by ext j; simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp [seedRow]
end ThreeSum.TernaryOriginalRowMenu
