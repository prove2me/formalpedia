-- Prove2me | solution 1 for Plasticity.Plane.exists_linearIsometryEquiv_of_radial_le
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-19T19:03:46.787416+00:00
-- url     : https://prove2.me/submissions/8fc49969-f5b9-4c50-a07f-abe1a04674f7

import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Dimension.Finrank
import Theorems.Thm_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_corner
import Theorems.Thm_Plasticity_Plane_exists_linearIsometryEquiv_of_radial_le_uncountable
import Theorems.Thm_Plasticity_Plane_exists_adjacent_edges_of_countable

theorem solution {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hV : Module.finrank ℝ V = 2) (hW : Module.finrank ℝ W = 2) (g : W → V)
    (hext : Set.MapsTo g (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1))
      (Set.extremePoints ℝ (Metric.closedBall (0 : V) 1)))
    (hrad : ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1),
      ∀ w' ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), ∀ α β : ℝ,
        ‖α • w + β • w'‖ ≤ ‖α • g w + β • g w'‖) :
    ∃ L : V ≃ₗᵢ[ℝ] W, ∀ w ∈ Set.extremePoints ℝ (Metric.closedBall (0 : W) 1), L (g w) = w := by
  by_cases hcount : (Set.extremePoints ℝ (Metric.closedBall (0 : W) 1)).Countable
  · obtain ⟨a, ha, b, hb, c, hc, hab, hbc, hac, hab2, hbc2⟩ :=
      Plasticity.Plane.exists_adjacent_edges_of_countable hW hcount
    exact Plasticity.Plane.exists_linearIsometryEquiv_of_radial_le_corner hV hW g hext hrad
      ha hb hc hab hbc hac hab2 hbc2
  · refine Plasticity.Plane.exists_linearIsometryEquiv_of_radial_le_uncountable hV hW g
      (fun w hw => ?_) hrad hcount
    have := (hext hw).1
    simpa using this
