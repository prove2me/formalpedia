-- Prove2me | solution 1 for Plasticity.A01.averaged_covers
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-14T08:07:49.621473+00:00
-- url     : https://prove2.me/submissions/49069520-13ca-4fc5-bf69-da9056f226dc

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting

namespace Sol_Plasticity_A01_averaged_covers

variable {X : Type*} [NormedAddCommGroup X]

/-- A `1`-Lipschitz map on `s`, stated with norms. -/
lemma lip_norm {F : X → X} {s : Set X} (hlip : LipschitzOnWith 1 F s) {x y : X}
    (hx : x ∈ s) (hy : y ∈ s) : ‖F x - F y‖ ≤ ‖x - y‖ := by
  have h := hlip.dist_le_mul x hx y hy
  simpa [dist_eq_norm] using h

/-- The radius `max ‖x‖ 1` used by the radial extension. -/
noncomputable def rad (x : X) : ℝ := max ‖x‖ 1

lemma one_le_rad (x : X) : 1 ≤ rad x := le_max_right _ _

lemma rad_pos (x : X) : 0 < rad x := lt_of_lt_of_le one_pos (one_le_rad x)

lemma norm_le_rad (x : X) : ‖x‖ ≤ rad x := le_max_left _ _

lemma rad_sub_le (x y : X) : rad x - rad y ≤ ‖x - y‖ := by
  have h1 := abs_max_sub_max_le_abs ‖x‖ ‖y‖ (1 : ℝ)
  have h2 := abs_norm_sub_norm_le x y
  have h3 := le_abs_self (rad x - rad y)
  unfold rad at *
  linarith

lemma scaled_mem [NormedSpace ℝ X] (x : X) : (rad x)⁻¹ • x ∈ Metric.closedBall (0 : X) 1 := by
  rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (rad_pos x),
    inv_mul_le_iff₀ (rad_pos x), mul_one]
  exact norm_le_rad x

/-- The radial extension `K̂ x = r_x • K (r_x⁻¹ • x)`, `r_x = max ‖x‖ 1`. -/
noncomputable def Khat [NormedSpace ℝ X] (K : X → X) (x : X) : X := rad x • K ((rad x)⁻¹ • x)

/-- The Lipschitz estimate for `K̂` when `r_y ≤ r_x`. -/
lemma Khat_lip_aux [NormedSpace ℝ X] (K : X → X)
    (hmaps : Set.MapsTo K (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1))
    (hlip : LipschitzOnWith 1 K (Metric.closedBall (0 : X) 1))
    (x y : X) (hxy : rad y ≤ rad x) :
    ‖Khat K x - Khat K y‖ ≤ 3 * ‖x - y‖ := by
  obtain ⟨r, hr⟩ : ∃ r, r = rad x := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = rad y := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = r⁻¹ • x := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = t⁻¹ • y := ⟨_, rfl⟩
  have hr0 : 0 < r := hr ▸ rad_pos x
  have ht0 : 0 < t := ht ▸ rad_pos y
  have hpB : p ∈ Metric.closedBall (0 : X) 1 := by rw [hp, hr]; exact scaled_mem x
  have hqB : q ∈ Metric.closedBall (0 : X) 1 := by rw [hq, ht]; exact scaled_mem y
  have hKq : ‖K q‖ ≤ 1 := by simpa using hmaps hqB
  have hKpq : ‖K p - K q‖ ≤ ‖p - q‖ := lip_norm hlip hpB hqB
  have hKx : Khat K x = r • K p := by rw [hp, hr]; rfl
  have hKy : Khat K y = t • K q := by rw [hq, ht]; rfl
  have hdecomp : Khat K x - Khat K y = r • (K p - K q) + (r - t) • K q := by
    rw [hKx, hKy, smul_sub, sub_smul]; abel
  have hrpq : r • (p - q) = (x - y) + (1 - r * t⁻¹) • y := by
    rw [hp, hq, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, sub_smul,
      one_smul]
    abel
  have htr : t ≤ r := by rw [hr, ht]; exact hxy
  have hcoef : 1 ≤ r * t⁻¹ := by
    rw [le_mul_inv_iff₀ ht0, one_mul]; exact htr
  have hy_le : ‖y‖ ≤ t := ht ▸ norm_le_rad y
  have hnorm_rpq : r * ‖p - q‖ ≤ ‖x - y‖ + (r - t) := by
    have hrn : r * ‖p - q‖ = ‖r • (p - q)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    rw [hrn, hrpq]
    calc ‖(x - y) + (1 - r * t⁻¹) • y‖ ≤ ‖x - y‖ + ‖(1 - r * t⁻¹) • y‖ := norm_add_le _ _
      _ = ‖x - y‖ + (r * t⁻¹ - 1) * ‖y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_sub]
      _ ≤ ‖x - y‖ + (r * t⁻¹ - 1) * t := by
          gcongr
      _ = ‖x - y‖ + (r - t) := by
          rw [sub_mul, mul_assoc, inv_mul_cancel₀ ht0.ne', mul_one, one_mul]
  have hrt : r - t ≤ ‖x - y‖ := by rw [hr, ht]; exact rad_sub_le x y
  calc ‖Khat K x - Khat K y‖ = ‖r • (K p - K q) + (r - t) • K q‖ := by rw [hdecomp]
    _ ≤ ‖r • (K p - K q)‖ + ‖(r - t) • K q‖ := norm_add_le _ _
    _ = r * ‖K p - K q‖ + (r - t) * ‖K q‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr0,
          abs_of_nonneg (by linarith)]
    _ ≤ r * ‖p - q‖ + (r - t) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hKpq hr0.le)
          (mul_le_mul_of_nonneg_left hKq (by linarith))
    _ ≤ 3 * ‖x - y‖ := by linarith

/-- `K̂` is `3`-Lipschitz on all of `X`. -/
lemma Khat_lip [NormedSpace ℝ X] (K : X → X)
    (hmaps : Set.MapsTo K (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1))
    (hlip : LipschitzOnWith 1 K (Metric.closedBall (0 : X) 1)) (x y : X) :
    ‖Khat K x - Khat K y‖ ≤ 3 * ‖x - y‖ := by
  rcases le_total (rad y) (rad x) with h | h
  · exact Khat_lip_aux K hmaps hlip x y h
  · rw [norm_sub_rev, norm_sub_rev x y]
    exact Khat_lip_aux K hmaps hlip y x h

end Sol_Plasticity_A01_averaged_covers

open Sol_Plasticity_A01_averaged_covers in
theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (K : X → X)
    (hmaps : Set.MapsTo K (Metric.closedBall (0 : X) 1) (Metric.closedBall (0 : X) 1))
    (hlip : LipschitzOnWith 1 K (Metric.closedBall (0 : X) 1))
    (α d : ℝ) (hα0 : 0 < α) (hα1 : α < 1 / 4) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hd : ∀ a ∈ Metric.sphere (0 : X) 1, 1 - d ≤ ‖(1 - α) • a + α • K a‖)
    (y : X) (hy : ‖y‖ ≤ 1 - d) :
    ∃ x ∈ Metric.closedBall (0 : X) 1, (1 - α) • x + α • K x = y := by
  -- The map `Φ z = y - α (K̂ z - z)` is a contraction with constant `4α`.
  let Φ : X → X := fun z => y - α • (Khat K z - z)
  have hΦ : ContractingWith (Real.toNNReal (4 * α)) Φ := by
    refine ⟨?_, ?_⟩
    · rw [Real.toNNReal_lt_one]; linarith
    · apply LipschitzWith.of_dist_le'
      intro z w
      simp only [Φ, dist_eq_norm]
      have hexp : y - α • (Khat K z - z) - (y - α • (Khat K w - w))
          = α • ((Khat K w - Khat K z) - (w - z)) := by
        simp only [smul_sub]; abel
      rw [hexp, norm_smul, Real.norm_eq_abs, abs_of_pos hα0]
      have h1 := Khat_lip K hmaps hlip w z
      have h2 := norm_sub_le (Khat K w - Khat K z) (w - z)
      rw [norm_sub_rev w z] at h1 h2
      calc α * ‖Khat K w - Khat K z - (w - z)‖ ≤ α * (4 * ‖z - w‖) :=
            mul_le_mul_of_nonneg_left (by linarith) hα0.le
        _ = 4 * α * ‖z - w‖ := by ring
  -- Its fixed point solves `(1 - α) x + α K̂ x = y`.
  obtain ⟨x0, hx0def⟩ : ∃ x0, x0 = ContractingWith.fixedPoint Φ hΦ := ⟨_, rfl⟩
  have hfix : Φ x0 = x0 := by rw [hx0def]; exact hΦ.fixedPoint_isFixedPt
  have heq : (1 - α) • x0 + α • Khat K x0 = y := by
    have h := sub_eq_iff_eq_add.mp hfix
    rw [h, sub_smul, one_smul, smul_sub]
    abel
  by_cases hx0 : ‖x0‖ ≤ 1
  · -- Inside the ball `K̂ = K`.
    have hr : rad x0 = 1 := max_eq_right hx0
    have hK : Khat K x0 = K x0 := by
      rw [show Khat K x0 = rad x0 • K ((rad x0)⁻¹ • x0) from rfl, hr, inv_one, one_smul,
        one_smul]
    refine ⟨x0, by simpa using hx0, ?_⟩
    rw [← hK]; exact heq
  · -- Outside the ball the equation contradicts the hypothesis on the sphere.
    exfalso
    replace hx0 : 1 < ‖x0‖ := not_le.mp hx0
    have hn0 : 0 < ‖x0‖ := by linarith
    have hr : rad x0 = ‖x0‖ := max_eq_left hx0.le
    obtain ⟨u, hu⟩ : ∃ u, u = ‖x0‖⁻¹ • x0 := ⟨_, rfl⟩
    have hus : u ∈ Metric.sphere (0 : X) 1 := by
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn0.ne']
    have hKx : Khat K x0 = ‖x0‖ • K u := by
      rw [show Khat K x0 = rad x0 • K ((rad x0)⁻¹ • x0) from rfl, hr, hu]
    have hxu : x0 = ‖x0‖ • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]
    have hid : (1 - α) • x0 + α • Khat K x0 = ‖x0‖ • ((1 - α) • u + α • K u) := by
      rw [hKx, smul_add, smul_comm ‖x0‖ (1 - α) u, smul_comm ‖x0‖ α (K u), ← hxu]
    have hbound := hd u hus
    have hnorm : ‖y‖ = ‖x0‖ * ‖(1 - α) • u + α • K u‖ := by
      rw [← heq, hid, norm_smul, norm_norm]
    nlinarith [mul_le_mul_of_nonneg_left hbound hn0.le,
      mul_pos (sub_pos.mpr hx0) (sub_pos.mpr hd1)]
