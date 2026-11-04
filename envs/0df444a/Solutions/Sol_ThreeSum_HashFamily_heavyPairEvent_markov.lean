-- Prove2me | solution 1 for ThreeSum.HashFamily.heavyPairEvent_markov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:06:41.381213+00:00
-- url     : https://prove2.me/submissions/7f34eb75-afe3-4e01-a39f-8a9660b37e48

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
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution (s t : α → Bool) (a b : K)
    (vertices : Finset (α → Bool)) (B : ℕ) :
    B * (heavyPairEvent s t a b vertices B).card ≤ loadedPairMass s t a b vertices := by
  calc
    _ = ∑ _w ∈ heavyPairEvent s t a b vertices B, B := by simp [Nat.mul_comm]
    _ ≤ ∑ w ∈ heavyPairEvent s t a b vertices B, bucketSize vertices w a := by
      apply Finset.sum_le_sum
      intro w hw
      exact (Finset.mem_filter.mp hw).2.le
    _ ≤ loadedPairMass s t a b vertices := by
      unfold loadedPairMass
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun w hw hnot => Nat.zero_le _)
end ThreeSum.HashFamily
