-- Prove2me | solution 1 for ThreeSum.HashFamily.sum_incidenceCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:36.957285+00:00
-- url     : https://prove2.me/submissions/6cb167c9-25f0-4be2-b3c8-deaa1f432fa0

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
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_incidenceCount_eq_sum
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]
namespace ThreeSum.HashFamily
theorem _root_.solution (events : E → Finset Ω) :
    (∑ w, incidenceCount events w) = ∑ e, (events e).card := by
  simp only [incidenceCount_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp
end ThreeSum.HashFamily
