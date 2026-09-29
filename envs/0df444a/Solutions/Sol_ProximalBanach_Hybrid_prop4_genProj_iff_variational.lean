-- Prove2me | solution 1 for ProximalBanach.Hybrid.prop4_genProj_iff_variational
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:37:36.513218+00:00
-- url     : https://prove2.me/submissions/65e0cf22-4921-4bb4-8dc8-cf04b2e73272

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

lemma aux_p4gp_normJ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : StrongDual ℝ E) (x : E) (hv : v ∈ dualityMap x) : ‖v‖ = ‖x‖ :=
  (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hv.2

lemma aux_p4gp_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : StrongDual ℝ E) (x y : E) (hv : v ∈ dualityMap x) :
    v y ≤ ‖x‖ * ‖y‖ := by
  rw [← aux_p4gp_normJ v x hv]
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using v.le_opNorm y)

lemma aux_p4gp_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : IsSmooth E) (w : StrongDual ℝ E) (x₀ d : E)
    (hw : w ∈ dualityMap x₀) :
    ∃ M, M ≤ 2 * w d ∧
      Tendsto (fun t : ℝ => (‖x₀ + t • d‖ ^ 2 - ‖x₀‖ ^ 2) / t) (𝓝[>] (0:ℝ)) (𝓝 M) := by
  by_cases hx : x₀ = 0
  · subst hx
    have hw0 : w = 0 := by
      have := aux_p4gp_normJ w 0 hw
      simpa using this
    refine ⟨0, by simp [hw0], ?_⟩
    have hc : Tendsto (fun t : ℝ => t * ‖d‖ ^ 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => t * ‖d‖ ^ 2) (𝓝 (0:ℝ)) (𝓝 (0 * ‖d‖ ^ 2)) :=
        (continuous_id.mul continuous_const).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0:ℝ) < t := ht
    rw [zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos ht']
    field_simp
    simp
  by_cases hd : d = 0
  · subst hd
    refine ⟨0, by simp, ?_⟩
    simp
  have ha : 0 < ‖x₀‖ := norm_pos_iff.mpr hx
  have hb : 0 < ‖d‖ := norm_pos_iff.mpr hd
  set a := ‖x₀‖ with ha_def
  set b := ‖d‖ with hb_def
  have hu : ‖a⁻¹ • x₀‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
    field_simp
    exact ha_def.symm
  have hv : ‖b⁻¹ • d‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hb]
    field_simp
    exact hb_def.symm
  obtain ⟨L, hL⟩ := hS _ _ hu hv
  have hmap : Tendsto (fun t : ℝ => (b / a) * t) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => (b / a) * t) (𝓝 (0:ℝ)) (𝓝 ((b / a) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_ne_zero (div_pos hb ha).ne' ht
  have hG : Tendsto (fun t : ℝ => (‖x₀ + t • d‖ - a) / t) (𝓝[≠] (0:ℝ)) (𝓝 (b * L)) := by
    have := (hL.comp hmap).const_mul b
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    simp only [Function.comp, hu]
    have hsm : a⁻¹ • x₀ + (b / a * t) • b⁻¹ • d = a⁻¹ • (x₀ + t • d) := by
      rw [smul_smul, smul_add, smul_smul]
      congr 2
      field_simp
    rw [hsm, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
    field_simp
  have hsub : ∀ t : ℝ, a ^ 2 + t * w d ≤ a * ‖x₀ + t • d‖ := by
    intro t
    have h1 := aux_p4gp_bound w x₀ (x₀ + t • d) hw
    have h2 : w (x₀ + t • d) = a ^ 2 + t * w d := by
      rw [map_add, map_smul, hw.1, smul_eq_mul]
    linarith
  have hle : b * L ≤ w d / a := by
    have hG' := hG.mono_left (nhdsWithin_mono (0:ℝ)
      (fun t (ht : t ∈ Set.Iio (0:ℝ)) => (ne_of_lt ht : t ≠ 0)))
    refine le_of_tendsto hG' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t < 0 := ht
    rw [div_le_iff_of_neg ht', div_mul_eq_mul_div, div_le_iff₀ ha]
    nlinarith [hsub t]
  have hsum : Tendsto (fun t : ℝ => ‖x₀ + t • d‖ + a) (𝓝[>] (0:ℝ)) (𝓝 (a + a)) := by
    have : Tendsto (fun t : ℝ => ‖x₀ + t • d‖ + a) (𝓝 (0:ℝ))
        (𝓝 (‖x₀ + (0:ℝ) • d‖ + a)) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).norm.add
        continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine ⟨b * L * (a + a), ?_, ?_⟩
  · have : b * L * (a + a) ≤ w d / a * (a + a) :=
      mul_le_mul_of_nonneg_right hle (by linarith)
    calc _ ≤ w d / a * (a + a) := this
      _ = 2 * w d := by field_simp; ring
  · have hG'' := hG.mono_left (nhdsWithin_mono (0:ℝ)
      (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => (ne_of_gt ht : t ≠ 0)))
    refine (hG''.mul hsum).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ne_of_gt ht
    field_simp
    ring

end ProximalBanach.Hybrid

open ProximalBanach.Hybrid
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hS : IsSmooth E) (J : E → StrongDual ℝ E)
    (hJ : ∀ x, J x ∈ dualityMap x) (C : Set E) (hcv : Convex ℝ C) (x x₀ : E)
    (hx₀ : x₀ ∈ C) :
    (∀ z ∈ C, phi J x₀ x ≤ phi J z x) ↔ ∀ z ∈ C, 0 ≤ (J x₀ - J x) (z - x₀) := by
  constructor
  · intro h z hz
    obtain ⟨M, hM, hT⟩ := aux_p4gp_deriv hS (J x₀) x₀ (z - x₀) (hJ x₀)
    have hge : 2 * J x (z - x₀) ≤ M := by
      refine ge_of_tendsto hT ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with t ht
      have hmem : x₀ + t • (z - x₀) ∈ C := hcv.add_smul_sub_mem hx₀ hz ⟨ht.1.le, ht.2.le⟩
      have h1 := h _ hmem
      unfold phi at h1
      rw [map_add, map_smul, smul_eq_mul] at h1
      rw [le_div_iff₀ ht.1]
      linarith
    simp only [ContinuousLinearMap.sub_apply]
    linarith
  · intro h z hz
    have h1 := h z hz
    simp only [ContinuousLinearMap.sub_apply, map_sub] at h1
    have h2 := aux_p4gp_bound (J x₀) x₀ z (hJ x₀)
    have h3 := (hJ x₀).1
    unfold phi
    nlinarith [sq_nonneg (‖z‖ - ‖x₀‖)]
