-- Prove2me | solution 1 for Plasticity.BallMap.map_zero_of_surjOn
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T19:03:27.27797+00:00
-- url     : https://prove2.me/submissions/8c7d94e4-d382-47d3-98a6-c84f52eaccc0

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# A nonexpansive surjection of unit balls fixes the origin

Cf. Cascales–Kadets–Orihuela–Wingler, RACSAM 2016, Theorem 2.3; Zavarzina, arXiv:1704.06961,
Theorem 2.3. Split from the proof of U01.
-/

namespace Sol_Plasticity_BallMap_map_zero_of_surjOn

/-- A `1`-Lipschitz map on `s`, stated with norms. -/
lemma lip_norm {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {F : X → Y}
    {s : Set X} (hlip : LipschitzOnWith 1 F s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F x - F y‖ ≤ ‖x - y‖ := by
  have h := hlip.dist_le_mul x hx y hy
  simpa [dist_eq_norm] using h

end Sol_Plasticity_BallMap_map_zero_of_surjOn

open Sol_Plasticity_BallMap_map_zero_of_surjOn in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : X → Y)
    (hsurj : Set.SurjOn F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1)) :
    F 0 = 0 := by
  have h0mem : (0 : X) ∈ Metric.closedBall (0 : X) 1 := by simp
  -- a preimage of the unit vector opposite to `F 0` would be too far from `0`
  by_contra hne
  have hn : ‖F 0‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  set v : Y := -(‖F 0‖⁻¹ • F 0) with hv
  have hvB : v ∈ Metric.closedBall (0 : Y) 1 := by
    simp [v, norm_smul, hn]
  obtain ⟨a, ha, hFa⟩ := hsurj hvB
  have h1 := lip_norm hlip ha h0mem
  rw [hFa, sub_zero] at h1
  have ha1 : ‖a‖ ≤ 1 := by simpa using ha
  have hvF : ‖v - F 0‖ = 1 + ‖F 0‖ := by
    have hsub : v - F 0 = -((‖F 0‖⁻¹ + 1) • F 0) := by
      simp only [v, add_smul, one_smul]; abel
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul,
      inv_mul_cancel₀ hn, one_mul]
  have hnpos : 0 < ‖F 0‖ := norm_pos_iff.mpr hne
  linarith
