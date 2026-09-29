-- Prove2me | solution 1 for ProximalBanach.Hybrid.prop5_three_point
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:34:40.578038+00:00
-- url     : https://prove2.me/submissions/32e7dd3a-4c58-48ca-b651-3d9abb2dce5f

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

lemma aux_p5tp_subgrad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : E} {v : StrongDual ℝ E} (hv : v ∈ dualityMap q) (z : E) :
    2 * v (z - q) ≤ ‖z‖ ^ 2 - ‖q‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := hv
  have hn : ‖v‖ = ‖q‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  have hvz : v z ≤ ‖q‖ * ‖z‖ := by
    have := v.le_opNorm z
    rw [Real.norm_eq_abs, hn] at this
    exact (le_abs_self _).trans this
  rw [map_sub, h1]
  nlinarith [sq_nonneg (‖z‖ - ‖q‖)]

lemma aux_p5tp_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : IsSmooth E) (q d : E) :
    ∃ L : ℝ, Tendsto (fun t : ℝ => (‖q + t • d‖ ^ 2 - ‖q‖ ^ 2) / t) (𝓝[≠] (0:ℝ)) (𝓝 L) := by
  by_cases hq : q = 0
  · subst hq
    refine ⟨0, ?_⟩
    have h0 : Tendsto (fun t : ℝ => t * ‖d‖ ^ 2) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => t * ‖d‖ ^ 2) (𝓝 (0:ℝ)) (𝓝 (0 * ‖d‖ ^ 2)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
    rw [zero_add, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_zero]
    field_simp
    ring
  by_cases hd : d = 0
  · subst hd
    refine ⟨0, ?_⟩
    simp only [smul_zero, add_zero, sub_self, zero_div]
    exact tendsto_const_nhds
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hu : ‖‖q‖⁻¹ • q‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hqn.ne']
  have hw : ‖‖d‖⁻¹ • d‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hdn.ne']
  obtain ⟨L0, hL0⟩ := hS _ _ hu hw
  have hc : 0 < ‖d‖ / ‖q‖ := div_pos hdn hqn
  have hct : Tendsto (fun t : ℝ => ‖d‖ / ‖q‖ * t) (𝓝[≠] (0:ℝ)) (𝓝[≠] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => ‖d‖ / ‖q‖ * t) (𝓝 (0:ℝ)) (𝓝 (‖d‖ / ‖q‖ * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
      exact mul_ne_zero hc.ne' ht
  have h1 := (hL0.comp hct).const_mul ‖d‖
  have h2 : Tendsto (fun t : ℝ => ‖q + t • d‖ + ‖q‖) (𝓝[≠] (0:ℝ))
      (𝓝 (‖q + (0:ℝ) • d‖ + ‖q‖)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.add (continuous_id.smul continuous_const)).norm.add
      continuous_const).tendsto 0
  refine ⟨_, (h1.mul h2).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
  have key : q + t • d = ‖q‖ • (‖q‖⁻¹ • q + (‖d‖ / ‖q‖ * t) • (‖d‖⁻¹ • d)) := by
    rw [smul_add, smul_smul, smul_smul, smul_smul, mul_inv_cancel₀ hqn.ne', one_smul]
    congr 2
    field_simp
  have hnorm : ‖q + t • d‖ = ‖q‖ * ‖‖q‖⁻¹ • q + (‖d‖ / ‖q‖ * t) • (‖d‖⁻¹ • d)‖ := by
    rw [key, norm_smul, norm_norm]
  simp only [Function.comp, hu]
  rw [hnorm]
  field_simp
  ring

theorem aux_p5tp_main {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : IsSmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x) (C : Set E)
    (hcv : Convex ℝ C) (x q : E) (hq : IsGenProj J C x q) (y : E) (hy : y ∈ C) :
    J x (y - q) ≤ J q (y - q) := by
  obtain ⟨L, hL⟩ := aux_p5tp_limit hS q (y - q)
  have hB : ∀ t : ℝ, 0 < t → t ≤ 1 →
      2 * t * J x (y - q) ≤ ‖q + t • (y - q)‖ ^ 2 - ‖q‖ ^ 2 := by
    intro t ht0 ht1
    have hmem : q + t • (y - q) ∈ C := hcv.add_smul_sub_mem hq.1 hy ⟨ht0.le, ht1⟩
    have := hq.2 _ hmem
    unfold phi at this
    rw [map_add, map_smul, smul_eq_mul] at this
    linarith
  have hA : ∀ t : ℝ, 2 * t * J q (y - q) ≤ ‖q + t • (y - q)‖ ^ 2 - ‖q‖ ^ 2 := by
    intro t
    have := aux_p5tp_subgrad (hJ q) (q + t • (y - q))
    rwa [add_sub_cancel_left, map_smul, smul_eq_mul, ← mul_assoc] at this
  have h1 : 2 * J x (y - q) ≤ L := by
    have hL' := hL.mono_left
      (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Ioi (0:ℝ)) => (ht.ne' : t ≠ 0)))
    apply ge_of_tendsto hL'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    rw [le_div_iff₀ ht.1]
    have := hB t ht.1 ht.2.le
    linarith
  have h2 : L ≤ 2 * J q (y - q) := by
    have hL' := hL.mono_left
      (nhdsWithin_mono (0:ℝ) (fun t (ht : t ∈ Set.Iio (0:ℝ)) => (ht.ne : t ≠ 0)))
    apply le_of_tendsto hL'
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < 0)
    rw [div_le_iff_of_neg ht]
    have := hA t
    linarith
  linarith

end ProximalBanach.Hybrid

open ProximalBanach.Hybrid
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem solution [StrictConvexSpace ℝ E] (hR : IsReflexive E) (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x) (C : Set E)
    (hne : C.Nonempty) (hcl : IsClosed C) (hcv : Convex ℝ C) (x q : E)
    (hq : IsGenProj J C x q) :
    ∀ y ∈ C, phi J y q + phi J q x ≤ phi J y x := by
  intro y hy
  have hmain := aux_p5tp_main hS J hJ C hcv x q hq y hy
  have hqq : J q q = ‖q‖ ^ 2 := (hJ q).1
  unfold phi
  rw [map_sub, map_sub, hqq] at hmain
  linarith
