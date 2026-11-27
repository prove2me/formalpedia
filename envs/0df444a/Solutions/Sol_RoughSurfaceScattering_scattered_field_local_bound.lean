-- Prove2me | solution 1 for RoughSurfaceScattering.scattered_field_local_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-27T03:09:10.931401+00:00
-- url     : https://prove2.me/submissions/c3085ce2-50fd-4438-a242-b844d53358ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_scattered_field_joint_continuous

open MeasureTheory Metric Filter Topology
open RoughSurfaceScattering

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (kp km μ : ℝ)
    (hpar : ParamCond kp km μ) (U : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU : ∀ y ∈ Dplus f, IsTSPSolution f kp km μ (incData f (pointSource kp y)).1
      (incData f (pointSource kp y)).2 (U y).1 (U y).2)
    (x0 : R2) (hx0 : x0 ∈ Dplus f) :
    ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ y ∈ Metric.ball x0 r, ∀ x ∈ Metric.ball x0 r,
      ‖(U y).1 x‖ ≤ C ∧ ‖fderiv ℝ (U y).1 x‖ ≤ C := by
  obtain ⟨r, hr, h1, h2⟩ := scattered_field_joint_continuous f hf kp km μ hpar U hU x0 hx0
  have hK : IsCompact (closedBall x0 r ×ˢ closedBall x0 r) :=
    (isCompact_closedBall x0 r).prod (isCompact_closedBall x0 r)
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn h1
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn h2
  refine ⟨r, hr, max M1 M2, fun y hy x hx => ?_⟩
  have hp : (x, y) ∈ closedBall x0 r ×ˢ closedBall x0 r :=
    ⟨ball_subset_closedBall hx, ball_subset_closedBall hy⟩
  exact ⟨(hM1 _ hp).trans (le_max_left _ _), (hM2 _ hp).trans (le_max_right _ _)⟩
