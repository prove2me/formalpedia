-- Prove2me | solution 1 for Plasticity.BallMap.norm_map_eq_of_mapsTo_sphere
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T19:05:03.033011+00:00
-- url     : https://prove2.me/submissions/12b1623f-2c5d-4673-9412-d20bca2717a8

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Theorems.Thm_Plasticity_BallMap_norm_map_le

/-!
# A sphere-preserving nonexpansive surjection of unit balls preserves norms

Cf. Cascales–Kadets–Orihuela–Wingler, RACSAM 2016, Theorem 2.3; Zavarzina, arXiv:1704.06961,
Theorem 2.3. Split from the proof of U01; uses `Plasticity.BallMap.norm_map_le`.
-/

namespace Sol_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere

/-- A `1`-Lipschitz map on `s`, stated with norms. -/
lemma lip_norm {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {F : X → Y}
    {s : Set X} (hlip : LipschitzOnWith 1 F s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F x - F y‖ ≤ ‖x - y‖ := by
  have h := hlip.dist_le_mul x hx y hy
  simpa [dist_eq_norm] using h

end Sol_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere

open Sol_Plasticity_BallMap_norm_map_eq_of_mapsTo_sphere in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (x : X) (hx : x ∈ Metric.closedBall (0 : X) 1) :
    ‖F x‖ = ‖x‖ := by
  have hle := Plasticity.BallMap.norm_map_le F hsurj hlip x hx
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  refine le_antisymm hle ?_
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  -- compare with the unit vector `u = x / ‖x‖`: `1 = ‖F u‖ ≤ (1 - ‖x‖) + ‖F x‖`
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set u : X := ‖x‖⁻¹ • x with hu
  have hus : u ∈ Metric.sphere (0 : X) 1 := by
    simp [u, norm_smul, hxn.ne']
  have huB : u ∈ Metric.closedBall (0 : X) 1 := Metric.sphere_subset_closedBall hus
  have hFu : ‖F u‖ = 1 := by simpa using hsphere hus
  have hd := lip_norm hlip huB hx
  have hux : u - x = (‖x‖⁻¹ - 1) • x := by simp only [u, sub_smul, one_smul]
  have hinv : 1 ≤ ‖x‖⁻¹ := (one_le_inv₀ hxn).mpr hx1
  have hnorm_ux : ‖u - x‖ = 1 - ‖x‖ := by
    rw [hux, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hinv), sub_mul,
      inv_mul_cancel₀ hxn.ne', one_mul]
  have htri := norm_sub_norm_le (F u) (F x)
  linarith
