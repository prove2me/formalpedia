-- Prove2me | solution 1 for ShorNonsmooth.AlmostDiff.generalizedAlmostGradients_convex_bounded_closed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T13:24:13.206113+00:00
-- url     : https://prove2.me/submissions/659c635f-b6f9-4d8b-a179-2df3aa6addf7

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_AlmostDifferentiable
import Definitions.Def_ShorNonsmooth_AlmostDiff_almostGradients

set_option autoImplicit false

open ShorNonsmooth.AlmostDiff in
theorem cd784f8c_almostGradients_subset_closedBall {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : AlmostDifferentiable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ L : ℝ, almostGradients f x ⊆ Metric.closedBall 0 L := by
  obtain ⟨L, hL⟩ := hf.1 (Metric.ball x 1) Metric.isBounded_ball
  refine ⟨L, ?_⟩
  rintro g ⟨xs, hxs, -, hg⟩
  refine Metric.isClosed_closedBall.mem_of_mapClusterPt hg ?_
  have hev : ∀ᶠ k in Filter.atTop, xs k ∈ Metric.ball x 1 :=
    hxs.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
  filter_upwards [hev] with k hk
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖fderiv ℝ f (xs k)‖ ≤ L :=
    norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hk) hL
  simpa [gradient] using h1

open ShorNonsmooth.AlmostDiff in
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : AlmostDifferentiable f)
    (x : EuclideanSpace ℝ (Fin n)) :
    Convex ℝ (closure (convexHull ℝ (almostGradients f x))) ∧
      Bornology.IsBounded (closure (convexHull ℝ (almostGradients f x))) ∧
      IsClosed (closure (convexHull ℝ (almostGradients f x))) := by
  obtain ⟨L, hL⟩ := cd784f8c_almostGradients_subset_closedBall f hf x
  refine ⟨(convex_convexHull ℝ _).closure, ?_, isClosed_closure⟩
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := L)).subset ?_
  exact closure_minimal (convexHull_min hL (convex_closedBall 0 L)) Metric.isClosed_closedBall
