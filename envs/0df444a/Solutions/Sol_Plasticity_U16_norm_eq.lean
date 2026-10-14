-- Prove2me | solution 1 for Plasticity.U16.norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:06:35.588977+00:00
-- url     : https://prove2.me/submissions/6a256bd5-dbf4-4e80-b18a-4bdb36618416

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

namespace Sol_Plasticity_U16_norm_eq

/-- A `1`-Lipschitz map on `s`, stated with norms. -/
lemma lip_norm {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {F : X → Y}
    {s : Set X} (hlip : LipschitzOnWith 1 F s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
    ‖F x - F y‖ ≤ ‖x - y‖ := by
  have h := hlip.dist_le_mul x hx y hy
  simpa [dist_eq_norm] using h

end Sol_Plasticity_U16_norm_eq

open Sol_Plasticity_U16_norm_eq in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hmaps : Set.MapsTo F (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : Y) 1))
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (hcover : Metric.sphere (0 : Y) 1 ⊆ F '' Metric.closedBall (0 : X) 1) :
    F 0 = 0 ∧ ∀ x ∈ Metric.closedBall (0 : X) 1, ‖F x‖ = ‖x‖ := by
  have h0mem : (0 : X) ∈ Metric.closedBall (0 : X) 1 := by simp
  -- Step 1: `F 0 = 0`, using a preimage of the unit vector opposite to `F 0`.
  have hF0 : F 0 = 0 := by
    by_contra hne
    have hn : ‖F 0‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    have hnpos : 0 < ‖F 0‖ := norm_pos_iff.mpr hne
    set v : Y := -(‖F 0‖⁻¹ • F 0) with hv
    have hvs : v ∈ Metric.sphere (0 : Y) 1 := by
      simp [v, norm_smul, hn]
    obtain ⟨a, ha, hFa⟩ := hcover hvs
    have h1 := lip_norm hlip ha h0mem
    rw [hFa, sub_zero] at h1
    have ha1 : ‖a‖ ≤ 1 := by simpa using ha
    have hvF : ‖v - F 0‖ = 1 + ‖F 0‖ := by
      have hsub : v - F 0 = -((‖F 0‖⁻¹ + 1) • F 0) := by
        simp only [v, add_smul, one_smul]; abel
      rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), add_mul,
        inv_mul_cancel₀ hn, one_mul]
    linarith
  refine ⟨hF0, fun x hx => ?_⟩
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  -- Step 2: `‖F x‖ ≤ ‖x‖` from the Lipschitz bound at `0`.
  have hle : ‖F x‖ ≤ ‖x‖ := by
    have h := lip_norm hlip hx h0mem
    simpa [hF0] using h
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [hF0]
  -- Step 3: `‖F x‖ ≥ ‖x‖` by comparing with the unit vector `u = x / ‖x‖`.
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
