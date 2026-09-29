-- Prove2me | solution 1 for ProximalBanach.Hybrid.duality_single_valued
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:58:49.35567+00:00
-- url     : https://prove2.me/submissions/bca578e4-adb4-4d65-9132-99750a451ab1

import Mathlib
import Definitions.Def_ProximalBanach_Hybrid_Basic

namespace ProximalBanach.Hybrid

open Filter Topology

/-- If the directional limit exists, it equals `f y` for every norming functional `f` of `u`. -/
theorem aux_dsv_lim {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u y : E} (hu : ‖u‖ = 1) (f : StrongDual ℝ E) (hf1 : ‖f‖ ≤ 1) (hfu : f u = 1) {L : ℝ}
    (hL : Tendsto (fun t : ℝ => (‖u + t • y‖ - ‖u‖) / t) (𝓝[≠] (0 : ℝ)) (𝓝 L)) :
    L = f y := by
  have key : ∀ t : ℝ, t * f y ≤ ‖u + t • y‖ - ‖u‖ := by
    intro t
    have h1 : f (u + t • y) ≤ ‖u + t • y‖ := by
      have := f.le_of_opNorm_le hf1 (u + t • y)
      rw [Real.norm_eq_abs, one_mul] at this
      exact (le_abs_self _).trans this
    rw [map_add, map_smul, hfu, smul_eq_mul] at h1
    rw [hu]; linarith
  have hpos : Tendsto (fun t : ℝ => (‖u + t • y‖ - ‖u‖) / t) (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    hL.mono_left (nhdsWithin_mono _ (fun t (ht : 0 < t) => ne_of_gt ht))
  have hneg : Tendsto (fun t : ℝ => (‖u + t • y‖ - ‖u‖) / t) (𝓝[<] (0 : ℝ)) (𝓝 L) :=
    hL.mono_left (nhdsWithin_mono _ (fun t (ht : t < 0) => ne_of_lt ht))
  have h1 : f y ≤ L := by
    refine ge_of_tendsto hpos (eventually_nhdsWithin_of_forall fun t (ht : 0 < t) => ?_)
    rw [le_div_iff₀ ht, mul_comm]; exact key t
  have h2 : L ≤ f y := by
    refine le_of_tendsto hneg (eventually_nhdsWithin_of_forall fun t (ht : t < 0) => ?_)
    rw [div_le_iff_of_neg ht, mul_comm]; exact key t
  linarith

end ProximalBanach.Hybrid

open ProximalBanach.Hybrid
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hS : IsSmooth E) (x : E) :
    ∃! v : StrongDual ℝ E, v ∈ dualityMap x := by
  by_cases hx : x = 0
  · subst hx
    refine ⟨0, ⟨by simp, by simp⟩, fun v hv => ?_⟩
    have h2 := hv.2
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      pow_eq_zero_iff, norm_eq_zero] at h2
    exact h2
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨g, hg1, hgx⟩ := exists_dual_vector ℝ x hxn
  have hv0 : ‖x‖ • g ∈ dualityMap x := by
    refine ⟨?_, ?_⟩
    · rw [ContinuousLinearMap.smul_apply, hgx, smul_eq_mul]
      simp [sq]
    · rw [norm_smul, hg1, norm_norm, mul_one]
  -- uniqueness
  have uniq : ∀ v w : StrongDual ℝ E, v ∈ dualityMap x → w ∈ dualityMap x → v = w := by
    intro v w hv hw
    set u : E := ‖x‖⁻¹ • x with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxn]
    have normalize : ∀ z : StrongDual ℝ E, z ∈ dualityMap x →
        ‖‖x‖⁻¹ • z‖ ≤ 1 ∧ (‖x‖⁻¹ • z) u = 1 := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := hz
      have hzn : ‖z‖ = ‖x‖ := by
        have := (sq_eq_sq₀ (norm_nonneg z) (norm_nonneg x)).mp hz2
        exact this
      refine ⟨?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, hzn, inv_mul_cancel₀ hxn]
      · rw [ContinuousLinearMap.smul_apply, hu_def, map_smul, hz1, smul_eq_mul, smul_eq_mul]
        field_simp
    obtain ⟨hv1, hvu⟩ := normalize v hv
    obtain ⟨hw1, hwu⟩ := normalize w hw
    ext y
    by_cases hy : y = 0
    · simp [hy]
    have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    set y' : E := ‖y‖⁻¹ • y with hy'_def
    have hy' : ‖y'‖ = 1 := by
      rw [hy'_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn]
    obtain ⟨L, hL⟩ := hS u y' hu hy'
    have e1 := aux_dsv_lim hu _ hv1 hvu hL
    have e2 := aux_dsv_lim hu _ hw1 hwu hL
    have e : (‖x‖⁻¹ • v) y' = (‖x‖⁻¹ • w) y' := e1.symm.trans e2
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hy'_def,
      map_smul, map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at e
    have hxi : ‖x‖⁻¹ ≠ 0 := inv_ne_zero hxn
    have hyi : ‖y‖⁻¹ ≠ 0 := inv_ne_zero hyn
    have := mul_left_cancel₀ hxi e
    exact mul_left_cancel₀ hyi this
  exact ⟨_, hv0, fun w hw => uniq w _ hw hv0⟩
