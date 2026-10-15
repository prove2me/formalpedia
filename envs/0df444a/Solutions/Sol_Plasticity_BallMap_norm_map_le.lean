-- Prove2me | solution 1 for Plasticity.BallMap.norm_map_le
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T19:03:59.323977+00:00
-- url     : https://prove2.me/submissions/a6d66097-2fd4-4f40-8fd5-582e5649da01

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_Plasticity_BallMap_map_zero_of_surjOn

/-!
# A nonexpansive surjection of unit balls does not increase norms

Cf. Cascales–Kadets–Orihuela–Wingler, RACSAM 2016, Theorem 2.3; Zavarzina, arXiv:1704.06961,
Theorem 2.3. Split from the proof of U01; uses `Plasticity.BallMap.map_zero_of_surjOn`.
-/

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1) :
    ‖F x‖ ≤ ‖x‖ := by
  have hF0 : F 0 = 0 := Plasticity.BallMap.map_zero_of_surjOn F hsurj hlip
  have h0mem : (0 : X) ∈ Metric.closedBall (0 : X) 1 := by simp
  have h := hlip.dist_le_mul x hx 0 h0mem
  simpa [dist_eq_norm, hF0] using h
