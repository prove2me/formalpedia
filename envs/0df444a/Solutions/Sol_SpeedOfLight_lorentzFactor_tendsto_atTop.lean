-- Prove2me | solution 1 for SpeedOfLight.lorentzFactor_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:12:21.251727+00:00
-- url     : https://prove2.me/submissions/f8439de2-9353-420a-91aa-fba8867cb34f

import Mathlib
import Definitions.Def_SpeedOfLight_kinematics

open Filter Topology
open SpeedOfLight

theorem W2p_SpeedOfLight_velAdd_light_speed (c v : ℝ) (hc : 0 < c) (hv : |v| < c) :
    velAdd c c v = c := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hv
  have hcv : 0 < c + v := by linarith
  have hc0 := hc.ne'
  unfold velAdd
  have e : 1 + c * v / c ^ 2 = (c + v) / c := by field_simp <;> ring
  rw [e, div_div_eq_mul_div, mul_div_cancel_left₀ _ hcv.ne']

theorem W2p_SpeedOfLight_velAdd_lt_light_speed (c u v : ℝ) (hc : 0 < c) (hu : |u| < c)
    (hv : |v| < c) :
    |velAdd c u v| < c := by
  obtain ⟨u1, u2⟩ := abs_lt.mp hu
  obtain ⟨v1, v2⟩ := abs_lt.mp hv
  have hD : 0 < c ^ 2 + u * v := by
    nlinarith [mul_pos (sub_pos.mpr u2) (sub_pos.mpr v2),
      mul_pos (by linarith : 0 < c + u) (by linarith : 0 < c + v)]
  have hc2 : c ^ 2 ≠ 0 := by positivity
  unfold velAdd
  rw [show 1 + u * v / c ^ 2 = (c ^ 2 + u * v) / c ^ 2 by rw [add_div, div_self hc2],
    div_div_eq_mul_div, abs_div, abs_of_pos hD, div_lt_iff₀ hD, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < c ^ 2)]
  rcases abs_cases (u + v) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    nlinarith [mul_pos (mul_pos hc (sub_pos.mpr u2)) (sub_pos.mpr v2),
      mul_pos (mul_pos hc (by linarith : 0 < c + u)) (by linarith : 0 < c + v)]

theorem W2p_SpeedOfLight_boost_preserves_lorentzInterval (c v x t : ℝ) (hc : 0 < c)
    (hv : |v| < c) :
    lorentzInterval c (boost c v x t).1 (boost c v x t).2 = lorentzInterval c x t := by
  obtain ⟨v1, v2⟩ := abs_lt.mp hv
  have hv2 : v ^ 2 < c ^ 2 := by nlinarith
  have hc2 : c ^ 2 ≠ 0 := by positivity
  have ha : 0 < 1 - v ^ 2 / c ^ 2 := by
    rw [sub_pos, div_lt_one (by positivity)]; exact hv2
  have H2 : lorentzFactor c v ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2 := by
    unfold lorentzFactor
    rw [div_pow, one_pow, Real.sq_sqrt ha.le,
      show 1 - v ^ 2 / c ^ 2 = (c ^ 2 - v ^ 2) / c ^ 2 by rw [sub_div, div_self hc2],
      one_div_div, div_mul_cancel₀ _ (sub_pos.mpr hv2).ne']
  have H1 : c ^ 2 * (1 / c ^ 2) = 1 := by field_simp
  unfold lorentzInterval boost
  dsimp only
  linear_combination (-2 * lorentzFactor c v ^ 2 * v * x * t +
      lorentzFactor c v ^ 2 * v ^ 2 * x ^ 2 * (1 / c ^ 2) + x ^ 2 * (lorentzFactor c v ^ 2 - 1)) * H1
    + (t ^ 2 - x ^ 2 * (1 / c ^ 2)) * H2

theorem W2p_SpeedOfLight_lorentzFactor_tendsto_atTop (c : ℝ) (hc : 0 < c) :
    Tendsto (lorentzFactor c) (𝓝[<] c) atTop := by
  have hc2 : c ^ 2 ≠ 0 := by positivity
  have h1 : Tendsto (fun v : ℝ => Real.sqrt (1 - v ^ 2 / c ^ 2)) (𝓝[<] c) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : Continuous (fun v : ℝ => Real.sqrt (1 - v ^ 2 / c ^ 2)) := by fun_prop
      have := hcont.tendsto c
      rw [div_self hc2, sub_self, Real.sqrt_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT hc] with v hv
      obtain ⟨hv1, hv2⟩ := hv
      exact Set.mem_Ioi.mpr (Real.sqrt_pos.mpr (by
        rw [sub_pos, div_lt_one (by positivity)]; nlinarith))
  have e : lorentzFactor c = fun v => (Real.sqrt (1 - v ^ 2 / c ^ 2))⁻¹ := by
    funext v; simp [lorentzFactor]
  rw [e]
  exact tendsto_inv_nhdsGT_zero.comp h1

theorem W2p_SpeedOfLight_kineticEnergy_unbounded (c m : ℝ) (hc : 0 < c) (hm : 0 < m) (E : ℝ) :
    ∃ v : ℝ, 0 < v ∧ v < c ∧ E < kineticEnergy c m v := by
  have hT := W2p_SpeedOfLight_lorentzFactor_tendsto_atTop c hc
  have hev := (hT.eventually (eventually_gt_atTop (E / (m * c ^ 2) + 1))).and
    (Ioo_mem_nhdsLT hc : ∀ᶠ x in 𝓝[<] c, x ∈ Set.Ioo 0 c)
  obtain ⟨v, hv1, hv2⟩ := hev.exists
  refine ⟨v, hv2.1, hv2.2, ?_⟩
  unfold kineticEnergy
  have h3 : E / (m * c ^ 2) < lorentzFactor c v - 1 := by linarith
  rw [div_lt_iff₀ (by positivity)] at h3
  rw [mul_assoc]
  exact h3

theorem W2p_SpeedOfLight_speed_of_light_invariant_and_unattainable (c m : ℝ) (hc : 0 < c)
    (hm : 0 < m) :
    (∀ v : ℝ, |v| < c → velAdd c c v = c) ∧
    (∀ u v : ℝ, |u| < c → |v| < c → |velAdd c u v| < c) ∧
    (∀ E : ℝ, ∃ v : ℝ, 0 < v ∧ v < c ∧ E < kineticEnergy c m v) :=
  ⟨fun v hv => W2p_SpeedOfLight_velAdd_light_speed c v hc hv,
    fun u v hu hv => W2p_SpeedOfLight_velAdd_lt_light_speed c u v hc hu hv,
    fun E => W2p_SpeedOfLight_kineticEnergy_unbounded c m hc hm E⟩

theorem solution (c : ℝ) (hc : 0 < c) :
    Tendsto (lorentzFactor c) (𝓝[<] c) atTop := by
  apply W2p_SpeedOfLight_lorentzFactor_tendsto_atTop <;> assumption
