-- Prove2me | solution 1 for Plasticity.BallMap.mem_sphere_of_map_mem_sphere
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T19:04:31.209607+00:00
-- url     : https://prove2.me/submissions/dec72846-6b2c-462d-bce0-024f369ed3c0

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_Plasticity_BallMap_norm_map_le

/-!
# A nonexpansive surjection of unit balls pulls unit vectors back to unit vectors

Cf. Cascales–Kadets–Orihuela–Wingler, RACSAM 2016, Theorem 2.3; Zavarzina, arXiv:1704.06961,
Theorem 2.3. Split from the proof of U01.
-/

namespace Sol_Plasticity_BallMap_mem_sphere_of_map_mem_sphere

/-- A `1`-Lipschitz map on `s`, stated with norms. -/
lemma lip_norm {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {F : X → Y}
    {s : Set X} (hlip : LipschitzOnWith 1 F s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F x - F y‖ ≤ ‖x - y‖ := by
  have h := hlip.dist_le_mul x hx y hy
  simpa [dist_eq_norm] using h

end Sol_Plasticity_BallMap_mem_sphere_of_map_mem_sphere

open Sol_Plasticity_BallMap_mem_sphere_of_map_mem_sphere in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1) (hs : F x ∈ Metric.sphere (0 : Y) 1) :
    x ∈ Metric.sphere (0 : X) 1 := by
  have hFx : ‖F x‖ = 1 := by simpa using hs
  -- a preimage `x'` of `-F x`: `2 = ‖F x - F x'‖ ≤ ‖x - x'‖ ≤ ‖x‖ + 1`
  have hnegB : -F x ∈ Metric.closedBall (0 : Y) 1 := by
    have h1 := Plasticity.BallMap.norm_map_le F hsurj hlip x hx
    have h2 : ‖x‖ ≤ 1 := by simpa using hx
    rw [mem_closedBall_zero_iff, norm_neg]
    linarith
  obtain ⟨x', hx', hFx'⟩ := hsurj hnegB
  have h := lip_norm hlip hx hx'
  rw [hFx', sub_neg_eq_add, ← two_smul ℝ (F x), norm_smul, hFx] at h
  have h3 := norm_sub_le x x'
  have h4 : ‖x'‖ ≤ 1 := by simpa using hx'
  have h5 : ‖x‖ ≤ 1 := by simpa using hx
  rw [mem_sphere_zero_iff_norm]
  norm_num at h
  linarith
