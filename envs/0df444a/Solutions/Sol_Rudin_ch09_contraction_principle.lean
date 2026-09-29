-- Prove2me | solution 1 for Rudin.ch09_contraction_principle
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:38:56.763793+00:00
-- url     : https://prove2.me/submissions/e1878dab-5a28-4652-93f0-ed97aab19a12

import Mathlib
open Filter Topology MeasureTheory


/-- Rudin, Theorem 9.23 (the contraction principle): a contraction of a nonempty complete metric
space into itself has a unique fixed point. -/
theorem solution {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (φ : X → X) (c : ℝ) (hc : c < 1) (hc0 : 0 ≤ c)
    (hφ : ∀ x y : X, dist (φ x) (φ y) ≤ c * dist x y) :
    ∃! x : X, φ x = x := by
  have h : ContractingWith ⟨c,hc0⟩ φ := ⟨hc,LipschitzWith.of_dist_le_mul hφ⟩
  exact ⟨h.fixedPoint φ,h.fixedPoint_isFixedPt,fun y hy => h.fixedPoint_unique hy⟩


#print axioms solution
