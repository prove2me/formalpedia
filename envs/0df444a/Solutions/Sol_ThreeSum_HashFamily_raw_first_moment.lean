-- Prove2me | solution 1 for ThreeSum.HashFamily.raw_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:08.996241+00:00
-- url     : https://prove2.me/submissions/ecc6c72e-1c57-4ff8-87f9-400a828002c9

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
import Theorems.Thm_ThreeSum_HashFamily_pairEvent_card
import Theorems.Thm_ThreeSum_HashFamily_sum_incidenceCount
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (left right : E → α → Bool)
    (hcross : ∀ e f, left e ≠ right f) (a b : K) :
    Fintype.card K ^ 2 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w) =
      Fintype.card E * Fintype.card (α × Bool → K) := by
  rw [sum_incidenceCount, Finset.mul_sum]
  simp_rw [pairEvent_card (hcross _ _) a b]
  simp
end ThreeSum.HashFamily
