-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P08.remarkTwo_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:28:02.862268+00:00
-- url     : https://prove2.me/submissions/9857df7c-003c-4da0-a767-66e0cbed4a36

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P08
noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

open QAlgorithms.Papers.Independent.Next46.P08

theorem g61d_scaled (F : ℝ → ℝ) (hF : MajorantRegularity F) (E : ℝ) (hE : 0 ≤ E) :
    Tendsto (fun x : ℝ => x * F (E / x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rcases hE.eq_or_lt with h0 | hpos
  · subst h0
    simp only [zero_div]
    have : Tendsto (fun x : ℝ => x * F 0) (nhds 0) (nhds (0 * F 0)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have hlo := hF.2.2.2
    have h1 : Tendsto (fun y : ℝ => F y / y) atTop (nhds 0) := hlo.tendsto_div_nhds_zero
    have h2 : Tendsto (fun x : ℝ => E / x) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
      have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hpos
      simpa [div_eq_mul_inv] using this
    have h3 := (h1.comp h2).const_mul E
    rw [mul_zero] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (x:ℝ) ≠ 0 := ne_of_gt hx
    simp only [Function.comp]
    field_simp

theorem g61d_g_cont : Continuous QAlgorithms.Papers.Independent.Claimed50.P39.g := by
  unfold QAlgorithms.Papers.Independent.Claimed50.P39.g
  exact (Real.continuous_mul_log.comp (continuous_id.add continuous_const)).sub
    Real.continuous_mul_log

theorem solution (F : ℝ → ℝ) (hF : MajorantRegularity F)
    (E : ℝ) (hE : 0 ≤ E) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun x : ℝ => x * F (E / x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    (∀ᶠ epsilon : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < epsilon ∧ t ≤ 1 / (2 * epsilon)) ∧
    Tendsto (fun epsilon : ℝ => holevoBound F E epsilon t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine ⟨g61d_scaled F hF E hE, ?_, ?_⟩
  · have hev : ∀ᶠ e : ℝ in nhds 0, e < 1 / (2 * t) :=
      eventually_lt_nhds (by positivity)
    filter_upwards [self_mem_nhdsWithin, hev.filter_mono nhdsWithin_le_nhds] with e he he2
    refine ⟨he, ?_⟩
    have he' : (0:ℝ) < e := he
    rw [le_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at he2
    linarith
  · -- the ratio is continuous at 0
    have hr : Tendsto (fun e : ℝ => continuityRatio e t) (nhds 0) (nhds (1 + t / 2)) := by
      have : ContinuousAt (fun e : ℝ => continuityRatio e t) 0 := by
        unfold continuityRatio
        exact continuousAt_const.div (continuousAt_const.sub (continuousAt_id.mul continuousAt_const))
          (by simp)
      simpa [continuityRatio] using this.tendsto
    have hr' := hr.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    -- epsilon * t → 0+
    have het : Tendsto (fun e : ℝ => e * t) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun e : ℝ => e * t) (nhds 0) (nhds (0 * t)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with e he
        exact mul_pos he ht
    have hA := (g61d_scaled F hF E hE).comp het
    -- e * F(E/(e t)) = t⁻¹ * ((e t) F(E/(e t)))
    have hB : Tendsto (fun e : ℝ => e * F (E / (e * t))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := hA.const_mul t⁻¹
      rw [mul_zero] at this
      refine this.congr' (Eventually.of_forall fun e => ?_)
      simp only [Function.comp]
      field_simp
    have hC : Tendsto (fun e : ℝ => (2 * t + continuityRatio e t) * (e * F (E / (e * t))))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 * t + (1 + t / 2)) * 0)) :=
      (tendsto_const_nhds.add hr').mul hB
    rw [mul_zero] at hC
    have hid : Tendsto (fun e : ℝ => e) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      nhdsWithin_le_nhds
    have hD : Tendsto (fun e : ℝ => 2 * QAlgorithms.Papers.Independent.Claimed50.P39.g
        (e * continuityRatio e t)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (2 * QAlgorithms.Papers.Independent.Claimed50.P39.g (0 * (1 + t / 2)))) :=
      ((g61d_g_cont.tendsto _).comp (hid.mul hr')).const_mul 2
    have hE' : Tendsto (fun e : ℝ => 2 * Real.binEntropy (e * t)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (2 * Real.binEntropy (0 * t))) :=
      ((Real.binEntropy_continuous.tendsto _).comp (hid.mul tendsto_const_nhds)).const_mul 2
    have hsum := (hC.add hD).add hE'
    have hg0 : QAlgorithms.Papers.Independent.Claimed50.P39.g 0 = 0 := by
      simp [QAlgorithms.Papers.Independent.Claimed50.P39.g]
    simp only [zero_mul, hg0, Real.binEntropy_zero, mul_zero, add_zero] at hsum
    refine hsum.congr' (Eventually.of_forall fun e => ?_)
    simp only [holevoBound]
    ring
