-- Prove2me | solution 1 for ThreeSum.HashFamily.trimmedPairEvent_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:04:27.739187+00:00
-- url     : https://prove2.me/submissions/4e3a2855-252c-4b37-98de-03774b40f297

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (s t : α → Bool) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool)) (B : ℕ) :
    trimmedPairEvent s t a b leftVertices rightVertices B ⊆ pairEvent s t a b :=
  Finset.filter_subset ..
end ThreeSum.HashFamily
