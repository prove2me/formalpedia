-- Prove2me | solution 1 for ProximalBanach.Hybrid.remark1_zeros_subset
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:15:25.176985+00:00
-- url     : https://prove2.me/submissions/bd2b9409-984a-4492-8876-a2e34dfd2b84

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

theorem aux_rz_subgrad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : StrongDual ℝ E) (p z : E) (hf : f ∈ dualityMap p) :
    2 * f (z - p) ≤ ‖z‖ ^ 2 - ‖p‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := hf
  have h3 : f z ≤ ‖f‖ * ‖z‖ := by
    have := f.le_opNorm z
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  rw [map_sub, h1]
  nlinarith [sq_nonneg (‖f‖ - ‖z‖)]

theorem aux_rz_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : IsSmooth E) (p d : E) :
    ∃ D : ℝ, Tendsto (fun t : ℝ => (‖p + t • d‖ ^ 2 - ‖p‖ ^ 2) / t) (𝓝[≠] (0 : ℝ)) (𝓝 D) := by
  by_cases hp : p = 0
  · subst hp
    refine ⟨0, ?_⟩
    have hc : Tendsto (fun t : ℝ => t * ‖d‖ ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun t : ℝ => t * ‖d‖ ^ 2) (𝓝 (0 : ℝ)) (𝓝 (0 * ‖d‖ ^ 2)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ht
    simp only [zero_add, norm_zero, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    field_simp
    ring
  by_cases hd : d = 0
  · subst hd
    refine ⟨0, ?_⟩
    simp only [smul_zero, add_zero, sub_self, zero_div]
    exact tendsto_const_nhds
  have ha : 0 < ‖p‖ := norm_pos_iff.2 hp
  have hb : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hx : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ ha.ne'
  have hy : ‖‖d‖⁻¹ • d‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hb.ne'
  obtain ⟨L, hL⟩ := hS (‖p‖⁻¹ • p) (‖d‖⁻¹ • d) hx hy
  have hφ : Tendsto (fun t : ℝ => t * ‖d‖ / ‖p‖) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => t * ‖d‖ / ‖p‖) (𝓝 (0 : ℝ)) (𝓝 (0 * ‖d‖ / ‖p‖)) :=
        ((continuous_id.mul continuous_const).div_const _).tendsto 0
      rw [zero_mul, zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_ne_zero (mul_ne_zero ht hb.ne') ha.ne'
  have h1 := hL.comp hφ
  have h2 : Tendsto (fun t : ℝ => ‖p + t • d‖ + ‖p‖) (𝓝[≠] (0 : ℝ)) (𝓝 (‖p‖ + ‖p‖)) := by
    have : Tendsto (fun t : ℝ => ‖p + t • d‖ + ‖p‖) (𝓝 (0 : ℝ))
        (𝓝 (‖p + (0 : ℝ) • d‖ + ‖p‖)) :=
      (((continuous_const.add (continuous_id.smul continuous_const)).norm).add
        continuous_const).tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine ⟨‖d‖ * L * (‖p‖ + ‖p‖), ?_⟩
  have h3 := (h1.const_mul ‖d‖).mul h2
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ht
  have key : ‖p‖⁻¹ • p + (t * ‖d‖ / ‖p‖) • ‖d‖⁻¹ • d = ‖p‖⁻¹ • (p + t • d) := by
    rw [smul_add, smul_smul, smul_smul]
    congr 2
    field_simp
  have hn : ‖‖p‖⁻¹ • p + (t * ‖d‖ / ‖p‖) • ‖d‖⁻¹ • d‖ = ‖p‖⁻¹ * ‖p + t • d‖ := by
    rw [key, norm_smul, norm_inv, norm_norm]
  simp only [Function.comp_apply, hn, hx]
  field_simp
  ring

theorem aux_rz_proj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hS : IsSmooth E) (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x) (x0 p d : E)
    (hmin : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖p‖ ^ 2 - 2 * J x0 p ≤ ‖p + t • d‖ ^ 2 - 2 * J x0 (p + t • d)) :
    (J x0 - J p) d ≤ 0 := by
  obtain ⟨D, hD⟩ := aux_rz_deriv hS p d
  have hA : 2 * J x0 d ≤ D := by
    have hD' : Tendsto (fun t : ℝ => (‖p + t • d‖ ^ 2 - ‖p‖ ^ 2) / t) (𝓝[>] (0 : ℝ)) (𝓝 D) :=
      hD.mono_left (nhdsWithin_mono _ (fun t (ht : 0 < t) => ht.ne'))
    refine ge_of_tendsto hD' ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have h := hmin t ht.1 ht.2.le
    rw [map_add, map_smul, smul_eq_mul] at h
    rw [le_div_iff₀ ht.1]
    nlinarith
  have hB : D ≤ 2 * J p d := by
    have hD' : Tendsto (fun t : ℝ => (‖p + t • d‖ ^ 2 - ‖p‖ ^ 2) / t) (𝓝[<] (0 : ℝ)) (𝓝 D) :=
      hD.mono_left (nhdsWithin_mono _ (fun t (ht : t < 0) => ht.ne))
    refine le_of_tendsto hD' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < 0)
    have h := aux_rz_subgrad (J p) p (p + t • d) (hJ p)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul] at h
    rw [div_le_iff_of_neg ht]
    nlinarith
  rw [ContinuousLinearMap.sub_apply]
  linarith

theorem aux_rz_H {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E → Set (StrongDual ℝ E)) (hT : IsMonotoneOp T) (J : E → StrongDual ℝ E) (r : ℕ → ℝ)
    (x y : ℕ → E) (v : ℕ → StrongDual ℝ E) (hrun : IsHybridRun T J r x y v) (n : ℕ) :
    zeros T ⊆ halfH v y n := by
  intro w hw
  have h := hT (y n) w (v n) (hrun n).1 0 hw
  show v n (w - y n) ≤ 0
  rw [sub_zero] at h
  have : v n (w - y n) = - v n (y n - w) := by rw [← map_neg, neg_sub]
  linarith

theorem aux_rz_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : StrongDual ℝ E) (c p w : E) (hp : f (p - c) ≤ 0) (hw : f (w - c) ≤ 0) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (p + t • (w - p) - c) ≤ 0 := by
  have : p + t • (w - p) - c = (1 - t) • (p - c) + t • (w - c) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  nlinarith [mul_nonneg ht0 (neg_nonneg.2 hw), mul_nonneg (sub_nonneg.2 ht1) (neg_nonneg.2 hp)]

end ProximalBanach.Hybrid

open ProximalBanach.Hybrid
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [StrictConvexSpace ℝ E] (hR : IsReflexive E) (hS : IsSmooth E)
    (J : E → StrongDual ℝ E) (hJ : ∀ x, J x ∈ dualityMap x)
    (T : E → Set (StrongDual ℝ E)) (hT : IsMaximalMonotone T) (hZ : (zeros T).Nonempty)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (x y : ℕ → E) (v : ℕ → StrongDual ℝ E)
    (hrun : IsHybridRun T J r x y v) :
    ∀ n : ℕ, zeros T ⊆ halfH v y n ∩ halfW J x n := by
  have hH := aux_rz_H T hT.1 J r x y v hrun
  intro n
  induction n with
  | zero =>
    intro w hw
    refine ⟨hH 0 hw, ?_⟩
    simp [halfW]
  | succ n ih =>
    intro w hw
    refine ⟨hH (n + 1) hw, ?_⟩
    obtain ⟨hpC, hmin⟩ := (hrun n).2.2
    have hwC := ih hw
    show (J (x 0) - J (x (n + 1))) (w - x (n + 1)) ≤ 0
    apply aux_rz_proj hS J hJ (x 0) (x (n + 1)) (w - x (n + 1))
    intro t ht0 ht1
    have hzC : x (n + 1) + t • (w - x (n + 1)) ∈ halfH v y n ∩ halfW J x n :=
      ⟨aux_rz_half (v n) (y n) (x (n + 1)) w hpC.1 hwC.1 t ht0.le ht1,
        aux_rz_half (J (x 0) - J (x n)) (x n) (x (n + 1)) w hpC.2 hwC.2 t ht0.le ht1⟩
    have := hmin _ hzC
    simp only [phi] at this
    linarith
