-- Prove2me | solution 1 for TikhonovHDD.Strong.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:31:48.881096+00:00
-- url     : https://prove2.me/submissions/60f897f2-8b69-4aaa-bb7e-2ad750397ad9

import Mathlib

set_option autoImplicit false

open Set Filter Topology

theorem solution (δ : ℝ) (hδ : 0 < δ) (f φ : ℝ → ℝ)
    (hf_int : MeasureTheory.IntegrableOn f (Ioi δ))
    (hf_nonneg : ∀ t ∈ Ioi δ, 0 ≤ f t)
    (hf_cont : ContinuousOn f (Ioi δ))
    (hφ_nonneg : ∀ t ∈ Ici δ, 0 ≤ φ t)
    (hφ_mono : MonotoneOn φ (Ici δ))
    (hφ_lim : Tendsto φ atTop atTop) :
    Tendsto (fun t => (φ t)⁻¹ * ∫ s in δ..t, φ s * f s) atTop (𝓝 0) := by
  -- interval integrability of f and φ * f
  have hfI : ∀ t, δ ≤ t → IntervalIntegrable f MeasureTheory.volume δ t := by
    intro t ht
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    exact hf_int.mono_set (Ioc_subset_Ioi_self)
  have hφI : ∀ t, δ ≤ t → IntervalIntegrable φ MeasureTheory.volume δ t := by
    intro t ht
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact hφ_mono.mono (Icc_subset_Ici_self)
  have hφfI : ∀ t, δ ≤ t → IntervalIntegrable (fun s => φ s * f s) MeasureTheory.volume δ t := by
    intro t ht
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
    have h1 : MeasureTheory.IntegrableOn f (Ioc δ t) := hf_int.mono_set (Ioc_subset_Ioi_self)
    have h2 : MeasureTheory.IntegrableOn φ (Ioc δ t) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp (hφI t ht)
    refine (h1.const_mul (φ t)).mono' (h2.aestronglyMeasurable.mul h1.aestronglyMeasurable) ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall ?_)
    intro s hs
    have hs1 : δ < s := hs.1
    have hφs : 0 ≤ φ s := hφ_nonneg s (le_of_lt hs1)
    have hfs : 0 ≤ f s := hf_nonneg s hs1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hφs hfs)]
    exact mul_le_mul_of_nonneg_right (hφ_mono (le_of_lt hs1) (le_trans (le_of_lt hs1) hs.2) hs.2) hfs
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose M
  have hconv := MeasureTheory.intervalIntegral_tendsto_integral_Ioi δ hf_int tendsto_id
  obtain ⟨M₀, hM₀⟩ := (hconv.eventually (lt_mem_nhds
    (show (∫ s in Ioi δ, f s) - ε / 2 < ∫ s in Ioi δ, f s by linarith))).exists_forall_of_atTop
  set M : ℝ := max M₀ (δ + 1) with hM
  have hMδ : δ < M := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hMgood : (∫ s in Ioi δ, f s) - ε / 2 < ∫ s in δ..M, f s := hM₀ M (le_max_left _ _)
  set C : ℝ := ∫ s in δ..M, φ s * f s with hC
  -- bound on tails
  have hbound : ∀ t, M ≤ t →
      (∫ s in δ..t, φ s * f s) ≤ C + φ t * (ε / 2) := by
    intro t ht
    have hsplit : (∫ s in δ..t, φ s * f s) = C + ∫ s in M..t, φ s * f s :=
      (intervalIntegral.integral_add_adjacent_intervals (hφfI M hMδ.le)
        ((hφfI t (le_trans hMδ.le ht)).mono_set (by
          rw [uIcc_of_le ht, uIcc_of_le (le_trans hMδ.le ht)]
          exact Icc_subset_Icc hMδ.le le_rfl))).symm
    have hfMt : IntervalIntegrable f MeasureTheory.volume M t :=
      (hfI t (le_trans hMδ.le ht)).mono_set (by
          rw [uIcc_of_le ht, uIcc_of_le (le_trans hMδ.le ht)]
          exact Icc_subset_Icc hMδ.le le_rfl)
    have h1 : (∫ s in M..t, φ s * f s) ≤ ∫ s in M..t, φ t * f s := by
      apply intervalIntegral.integral_mono_on ht
      · exact (hφfI t (le_trans hMδ.le ht)).mono_set (by
          rw [uIcc_of_le ht, uIcc_of_le (le_trans hMδ.le ht)]
          exact Icc_subset_Icc hMδ.le le_rfl)
      · exact hfMt.const_mul (φ t)
      · intro s hs
        have hs1 : δ < s := lt_of_lt_of_le hMδ hs.1
        exact mul_le_mul_of_nonneg_right (hφ_mono (le_of_lt hs1)
          (le_trans (le_of_lt hMδ) ht) hs.2) (hf_nonneg s hs1)
    rw [intervalIntegral.integral_const_mul] at h1
    -- ∫_M^t f ≤ ε/2
    have h2 : (∫ s in M..t, f s) = (∫ s in δ..t, f s) - ∫ s in δ..M, f s := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hfI M hMδ.le) hfMt]
      ring
    have h3 : (∫ s in δ..t, f s) ≤ ∫ s in Ioi δ, f s := by
      rw [intervalIntegral.integral_of_le (le_trans hMδ.le ht)]
      exact MeasureTheory.setIntegral_mono_set hf_int
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall hf_nonneg)) (Eventually.of_forall Ioc_subset_Ioi_self)
    have hφt : 0 ≤ φ t := hφ_nonneg t (le_trans hMδ.le (le_trans (le_refl _) ht))
    have h4 : φ t * (∫ s in M..t, f s) ≤ φ t * (ε / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hφt
    linarith
  have hnn : ∀ t, δ ≤ t → 0 ≤ ∫ s in δ..t, φ s * f s := by
    intro t ht
    rw [intervalIntegral.integral_of_le ht]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ioc (fun s hs => ?_)
    exact mul_nonneg (hφ_nonneg s (le_of_lt hs.1)) (hf_nonneg s hs.1)
  -- C / φ t → 0
  have hCt : Tendsto (fun t => C * (φ t)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hφ_lim).const_mul C
  have hev1 : ∀ᶠ t in atTop, C * (φ t)⁻¹ < ε / 2 :=
    hCt.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ t in atTop, 0 < φ t := hφ_lim.eventually_gt_atTop 0
  filter_upwards [hev1, hev2, eventually_ge_atTop M] with t h1 h2 h3
  have hδt : δ ≤ t := le_trans hMδ.le h3
  rw [Real.dist_eq, sub_zero]
  have hnn' := hnn t hδt
  have hpos : 0 ≤ (φ t)⁻¹ * ∫ s in δ..t, φ s * f s := mul_nonneg (inv_nonneg.mpr h2.le) hnn'
  rw [abs_of_nonneg hpos]
  calc (φ t)⁻¹ * ∫ s in δ..t, φ s * f s
      ≤ (φ t)⁻¹ * (C + φ t * (ε / 2)) := mul_le_mul_of_nonneg_left (hbound t h3) (inv_nonneg.mpr h2.le)
    _ = C * (φ t)⁻¹ + ε / 2 := by field_simp
    _ < ε := by linarith
