-- Prove2me | solution 1 for ThreeSum.TernaryOriginalRowMenu.vectorPoly_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:10:54.113191+00:00
-- url     : https://prove2.me/submissions/719ba861-6024-468e-83c2-fd1fca927d3d

import Definitions.Def_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField
import Definitions.Def_Submission_ThreeSum_TernaryOriginalRowMenu

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
theorem _root_.solution (Λ : ℕ) : Function.Injective (vectorPoly (K := K) (E := E) Λ) := by
  intro v w h
  have he := Polynomial.injective_ofFn Λ h
  funext i
  exact (algebraMap K E).injective (congrFun he i)
end ThreeSum.TernaryOriginalRowMenu
