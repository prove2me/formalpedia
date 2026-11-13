-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.pointwiseSummable_absolute
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T22:51:35.662695+00:00
-- url     : https://prove2.me/submissions/32647756-7ef9-45d1-9aa8-d060b7d30970

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.CategoryTheory.Category.Basic
set_option autoImplicit false


noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Lemma A.2, PDF p. 33: the absolute-value family is pointwise summable.
There is no continuity or local uniform convergence assertion here. -/
theorem solution
    (X : Type u) [TopologicalSpace X] (I : Type v) (phi : I → X → ℝ)
    (hphi : ∀ x, Summable (fun i => phi i x)) :
    ∀ x, Summable (fun i => |phi i x|) := by
  intro x
  exact (hphi x).abs
