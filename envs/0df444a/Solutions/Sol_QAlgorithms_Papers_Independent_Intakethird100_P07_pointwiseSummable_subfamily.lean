-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P07.pointwiseSummable_subfamily
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T22:53:13.157702+00:00
-- url     : https://prove2.me/submissions/4b59ea63-c031-4cb1-9223-b8e8deed7ffd

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.CategoryTheory.Category.Basic
set_option autoImplicit false


noncomputable section

universe u v



open CategoryTheory Topology TopologicalSpace

/-- Lemma A.1, PDF pp. 32–33: pointwise unconditional summability is
inherited by every subfamily in a complete Hausdorff abelian group. -/
theorem solution
    (X : Type u) [TopologicalSpace X] (I : Type v)
    (V : Type u) [AddCommGroup V] [UniformSpace V] [IsUniformAddGroup V]
    [CompleteSpace V] [T2Space V] (phi : I → X → V)
    (hphi : ∀ x, Summable (fun i => phi i x)) :
    ∀ (J : Set I) (x : X), Summable (fun j : J => phi j.val x) := by
  intro J x
  exact (hphi x).subtype J
