-- Prove2me | solution 1 for TwoAssumptions.prop3_manifold
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:21:30.298707+00:00
-- url     : https://prove2.me/submissions/a8cf208f-3e4a-4884-bd83-9a6a9bb0ee4c

import Mathlib
open scoped ContDiff
namespace TwoAssumptions

theorem _root_.solution (S : Type*) [TopologicalSpace S] (n : ℕ)
    (e : S ≃ₜ (EuclideanSpace ℝ (Fin n))) :
    Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) S) := by
  exact ⟨(e.toOpenPartialHomeomorph).singletonChartedSpace (by simp)⟩


end TwoAssumptions
