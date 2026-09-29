-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.fiber_ncard_le_max_totalDegree
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:43:51.888773+00:00
-- url     : https://prove2.me/submissions/359ae28b-b4de-4f02-afff-d79029c06659

import Mathlib
import Definitions.Def_PdzPrelim
import Theorems.Thm_PachDeZeeuw_Algebraic_specialized_natDegree_le_totalDegree

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (h : Specialized0 x p ≠ 0 ∨ Specialized0 x q ≠ 0) :
    (FiberCommonZeros x p q).ncard ≤ max p.totalDegree q.totalDegree := by
  rcases h with hp | hq
  · have hsub :
        FiberCommonZeros x p q ⊆ (Specialized0 x p).rootSet ℝ := by
      intro y hy
      rw [Polynomial.mem_rootSet]
      exact ⟨hp, by simpa [Polynomial.IsRoot] using hy.1⟩
    have hrootset_eq :
        ({y | Polynomial.IsRoot (Specialized0 x p) y} : Set ℝ) =
          (Specialized0 x p).rootSet ℝ := by
      ext y
      rw [Polynomial.mem_rootSet]
      constructor
      · intro hy
        exact ⟨hp, by simpa [Polynomial.IsRoot] using hy⟩
      · intro hy
        exact by simpa [Polynomial.IsRoot] using hy.2
    have hroot :
        ((Specialized0 x p).rootSet ℝ).ncard ≤ (Specialized0 x p).natDegree := by
      simpa using (Polynomial.ncard_rootSet_le (Specialized0 x p) ℝ)
    calc
      (FiberCommonZeros x p q).ncard ≤
          ((Specialized0 x p).rootSet ℝ).ncard := by
            exact Set.ncard_le_ncard hsub (hrootset_eq ▸ Polynomial.finite_setOfPred_isRoot hp)
      _ ≤ (Specialized0 x p).natDegree := hroot
      _ ≤ p.totalDegree := specialized_natDegree_le_totalDegree p x
      _ ≤ max p.totalDegree q.totalDegree := le_max_left _ _
  · have hsub :
        FiberCommonZeros x p q ⊆ (Specialized0 x q).rootSet ℝ := by
      intro y hy
      rw [Polynomial.mem_rootSet]
      exact ⟨hq, by simpa [Polynomial.IsRoot] using hy.2⟩
    have hrootset_eq :
        ({y | Polynomial.IsRoot (Specialized0 x q) y} : Set ℝ) =
          (Specialized0 x q).rootSet ℝ := by
      ext y
      rw [Polynomial.mem_rootSet]
      constructor
      · intro hy
        exact ⟨hq, by simpa [Polynomial.IsRoot] using hy⟩
      · intro hy
        exact by simpa [Polynomial.IsRoot] using hy.2
    have hroot :
        ((Specialized0 x q).rootSet ℝ).ncard ≤ (Specialized0 x q).natDegree := by
      simpa using (Polynomial.ncard_rootSet_le (Specialized0 x q) ℝ)
    calc
      (FiberCommonZeros x p q).ncard ≤
          ((Specialized0 x q).rootSet ℝ).ncard := by
            exact Set.ncard_le_ncard hsub (hrootset_eq ▸ Polynomial.finite_setOfPred_isRoot hq)
      _ ≤ (Specialized0 x q).natDegree := hroot
      _ ≤ q.totalDegree := specialized_natDegree_le_totalDegree q x
      _ ≤ max p.totalDegree q.totalDegree := le_max_right _ _
