-- Prove2me | solution 1 for ThreeSum.HashFamily.trimmed_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:30.39679+00:00
-- url     : https://prove2.me/submissions/8969c363-ead9-4381-8a96-a021bfff6c31

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
import Theorems.Thm_ThreeSum_HashFamily_incidenceCount_mono
import Definitions.Def_WeightedCache3SUM_Alias_cfb67b5df426cbfb
import Theorems.Thm_ThreeSum_HashFamily_trimmedPairEvent_subset

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (Bbad : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ Bbad)
    (hBp : Bbad ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) (leftVertices rightVertices : Finset (α → Bool)) (Bbucket : ℕ) :
    Fintype.card K ^ 2 * (∑ w, incidenceCount
        (fun e => trimmedPairEvent (left e) (right e) a b leftVertices rightVertices Bbucket) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by
  refine (Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun w hw => ?_))).trans
    (raw_second_moment_five left right hinj hcross Bbad hB hBp hEp a b)
  exact Nat.pow_le_pow_left (incidenceCount_mono
    (fun e => trimmedPairEvent_subset (left e) (right e) a b leftVertices rightVertices Bbucket) w) 2
end ThreeSum.HashFamily
