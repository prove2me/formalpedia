-- Prove2me | solution 1 for ThreeSum.HashFamily.trimmed_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:28:26.399639+00:00
-- url     : https://prove2.me/submissions/d8996341-0b0b-4c83-a5a3-fbce80a714ee

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
import Theorems.Thm_ThreeSum_HashFamily_sum_incidenceCount
import Definitions.Def_WeightedCache3SUM_Alias_9cba9841773c016e
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (left right : E → α → Bool)
    (hcross : ∀ e f, left e ≠ right f) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool))
    (hL : ∀ e u, u ∈ leftVertices → u ≠ right e)
    (hR : ∀ e u, u ∈ rightVertices → u ≠ left e)
    (B : ℕ)
    (hBL : 4 * (Fintype.card K + leftVertices.card) ≤ B * Fintype.card K)
    (hBR : 4 * (Fintype.card K + rightVertices.card) ≤ B * Fintype.card K) :
    Fintype.card E * Fintype.card (α × Bool → K) ≤
      2 * Fintype.card K ^ 2 * (∑ w, incidenceCount
        (fun e => trimmedPairEvent (left e) (right e) a b leftVertices rightVertices B) w) := by
  rw [sum_incidenceCount, Finset.mul_sum]
  calc
    _ = ∑ _e : E, Fintype.card (α × Bool → K) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun e he =>
      trimmedPairEvent_bound (hcross e e) a b leftVertices rightVertices (hL e) (hR e) B hBL hBR)
end ThreeSum.HashFamily
