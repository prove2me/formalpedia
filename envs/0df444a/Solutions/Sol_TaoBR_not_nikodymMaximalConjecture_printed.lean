-- Prove2me | solution 1 for TaoBR.not_nikodymMaximalConjecture_printed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:53:05.819443+00:00
-- url     : https://prove2.me/submissions/7869b65b-6020-4a64-9b1c-4ef632acfe11

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory Metric
open scoped SchwartzMap ENNReal

namespace TaoBR

lemma exists_bump (n : ℕ) : ∃ f : 𝓢(E n, ℝ), HasCompactSupport f ∧ (∀ x, f x ≤ 1) ∧
    (∀ x, 0 ≤ f x) ∧ ∀ x ∈ closedBall (0 : E n) 1, f x = 1 := by
  let b : ContDiffBump (0 : E n) := ⟨1, 2, by norm_num, by norm_num⟩
  refine ⟨b.hasCompactSupport.toSchwartzMap (b.contDiff), ?_, ?_, ?_, ?_⟩
  · exact b.hasCompactSupport
  · intro x; simpa using b.le_one
  · intro x; simpa using b.nonneg
  · intro x hx; simpa using b.one_of_mem_closedBall (by simpa using hx)

lemma tube_subset {n : ℕ} (δ : ℝ) (ω c : E n) (hω : ‖ω‖ = 1) :
    tube δ ω c ⊆ closedBall c (1 / 2 + δ) := by
  intro x hx
  obtain ⟨h1, h2⟩ := hx
  rw [mem_closedBall, dist_eq_norm]
  have : x - c = (x - c - inner ℝ (x - c) ω • ω) + inner ℝ (x - c) ω • ω := by abel
  calc ‖x - c‖ = ‖(x - c - inner ℝ (x - c) ω • ω) + inner ℝ (x - c) ω • ω‖ := by rw [← this]
    _ ≤ ‖x - c - inner ℝ (x - c) ω • ω‖ + ‖inner ℝ (x - c) ω • ω‖ := norm_add_le _ _
    _ ≤ δ + 1 / 2 := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs]; linarith
    _ = 1 / 2 + δ := by ring

lemma tube_measurable {n : ℕ} (δ : ℝ) (ω c : E n) : MeasurableSet (tube δ ω c) := by
  have : tube δ ω c = {x | |inner ℝ (x - c) ω| ≤ 1 / 2} ∩
      {x | ‖x - c - inner ℝ (x - c) ω • ω‖ ≤ δ} := rfl
  rw [this]
  refine MeasurableSet.inter (measurableSet_le ?_ ?_) (measurableSet_le ?_ ?_) <;> fun_prop

lemma tube_pos {n : ℕ} (δ : ℝ) (hδ : 0 < δ) (ω c : E n) (hω : ‖ω‖ = 1) :
    0 < volume (tube δ ω c) := by
  have hsub : ball c (min (δ / 2) (1 / 2)) ⊆ tube δ ω c := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    have hr1 : ‖x - c‖ < δ / 2 := lt_of_lt_of_le hx (min_le_left _ _)
    have hr2 : ‖x - c‖ < 1 / 2 := lt_of_lt_of_le hx (min_le_right _ _)
    have hin : |inner ℝ (x - c) ω| ≤ ‖x - c‖ := by
      have := abs_real_inner_le_norm (x - c) ω
      rwa [hω, mul_one] at this
    refine ⟨by linarith, ?_⟩
    calc ‖x - c - inner ℝ (x - c) ω • ω‖ ≤ ‖x - c‖ + ‖inner ℝ (x - c) ω • ω‖ := norm_sub_le _ _
      _ ≤ ‖x - c‖ + ‖x - c‖ := by
        rw [norm_smul, hω, mul_one, Real.norm_eq_abs]; linarith
      _ ≤ δ := by linarith
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  exact measure_ball_pos _ _ (lt_min (by linarith) (by norm_num))

lemma tube_finite {n : ℕ} (δ : ℝ) (ω c : E n) (hω : ‖ω‖ = 1) :
    volume (tube δ ω c) < ∞ :=
  lt_of_le_of_lt (measure_mono (tube_subset δ ω c hω)) measure_closedBall_lt_top

lemma tube_avg_le {n : ℕ} (δ : ℝ) (hδ : 0 < δ) (ω c : E n) (hω : ‖ω‖ = 1)
    (f : E n → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    (volume (tube δ ω c)).toReal⁻¹ * ∫ x in tube δ ω c, f x ≤ 1 := by
  have hpos : 0 < (volume (tube δ ω c)).toReal :=
    ENNReal.toReal_pos (tube_pos δ hδ ω c hω).ne' (tube_finite δ ω c hω).ne
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := tube δ ω c) (C := 1)
    (tube_finite δ ω c hω) (f := f) (fun x _ => by simpa using hf x)
  rw [Measure.real] at this
  have h2 : ∫ x in tube δ ω c, f x ≤ (volume (tube δ ω c)).toReal := by
    have := (le_abs_self _).trans this
    simpa using this
  calc _ ≤ (volume (tube δ ω c)).toReal⁻¹ * (volume (tube δ ω c)).toReal :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

lemma tube_avg_eq {n : ℕ} (δ : ℝ) (hδ : 0 < δ) (ω c : E n) (hω : ‖ω‖ = 1)
    (f : E n → ℝ) (hf : ∀ x ∈ tube δ ω c, f x = 1) :
    (volume (tube δ ω c)).toReal⁻¹ * ∫ x in tube δ ω c, f x = 1 := by
  have hpos : 0 < (volume (tube δ ω c)).toReal :=
    ENNReal.toReal_pos (tube_pos δ hδ ω c hω).ne' (tube_finite δ ω c hω).ne
  rw [setIntegral_congr_fun (tube_measurable δ ω c) (g := fun _ => (1 : ℝ)) hf]
  simp [Measure.real]
  exact inv_mul_cancel₀ hpos.ne'

/-- Shared tail: if `g δ` has `eLpNorm ≥ s > 0` for all small δ, the bound fails. -/
lemma not_small_bound {n : ℕ} (hn : 2 ≤ n) (s : ℝ≥0∞) (hs : 0 < s) (A : ℝ≥0∞) (hA : A ≠ ∞)
    (C δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (h : ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      s ≤ ENNReal.ofReal (C * δ ^ ((n : ℝ) / (1 : ℝ) - 1 - 1 / 2)) * A) : False := by
  have he : (0 : ℝ) < (n : ℝ) / (1 : ℝ) - 1 - 1 / 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [div_one]; linarith
  have ht : Filter.Tendsto (fun δ : ℝ => ENNReal.ofReal (C * δ ^ ((n : ℝ) / (1 : ℝ) - 1 - 1 / 2)) * A)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun δ : ℝ => C * δ ^ ((n : ℝ) / (1 : ℝ) - 1 - 1 / 2))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := ((Real.continuousAt_rpow_const 0 _ (Or.inr he.le)).tendsto.const_mul C)
      rw [Real.zero_rpow he.ne', mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := ENNReal.tendsto_ofReal h1
    simp only [ENNReal.ofReal_zero] at h2
    have := ENNReal.Tendsto.mul_const h2 (Or.inr hA)
    simpa using this
  have hev := (ht.eventually (gt_mem_nhds hs))
  have hev2 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < δ₀ :=
    (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hδ₀))
  obtain ⟨δ, h1, h2, h3⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
  exact absurd (h δ h3 h2) (not_le.2 h1)

lemma unit_vec (n : ℕ) (hn : 2 ≤ n) : ∃ ω : E n, ‖ω‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp⟩

theorem nikodym_dev (n : ℕ) (hn : 2 ≤ n) :
    ¬ ∀ p : ℝ, 1 ≤ p → p ≤ n → ∀ α : ℝ, 0 < α →
      ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∀ f : 𝓢(E n, ℝ), HasCompactSupport f →
        eLpNorm (nikodymMaximal δ f) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * δ ^ ((n : ℝ) / p - 1 - α)) * eLpNorm f (ENNReal.ofReal p) volume := by
  intro H
  obtain ⟨C, δ₀, hδ₀, hC⟩ := H 1 le_rfl (by exact_mod_cast (by omega : 1 ≤ n)) (1 / 2) (by norm_num)
  obtain ⟨f, hfc, hf1, hf0, hfeq⟩ := exists_bump n
  obtain ⟨ω₀, hω₀⟩ := unit_vec n hn
  have hA : eLpNorm f (ENNReal.ofReal 1) volume ≠ ∞ := by
    simpa using (f.memLp 1 volume).eLpNorm_lt_top.ne
  have hs : 0 < volume (closedBall (0 : E n) (1 / 4)) := measure_closedBall_pos _ _ (by norm_num)
  refine not_small_bound hn _ hs _ hA C (min δ₀ (1 / 4)) (lt_min hδ₀ (by norm_num)) ?_
  intro δ hδ hδ'
  have hδ1 : δ < δ₀ := lt_of_lt_of_le hδ' (min_le_left _ _)
  have hδ2 : δ < 1 / 4 := lt_of_lt_of_le hδ' (min_le_right _ _)
  refine le_trans ?_ (hC δ hδ hδ1 f hfc)
  rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm]
  calc volume (closedBall (0 : E n) (1 / 4))
      = ∫⁻ _ in closedBall (0 : E n) (1 / 4), 1 ∂volume := by simp
    _ ≤ ∫⁻ x in closedBall (0 : E n) (1 / 4), ‖nikodymMaximal δ f x‖ₑ ∂volume := by
      refine setLIntegral_mono' measurableSet_closedBall fun x hx => ?_
      have hx' : ‖x‖ ≤ 1 / 4 := by simpa using hx
      have hb : ∀ T : {T : E n × E n // ‖T.1‖ = 1 ∧ x ∈ tube δ T.1 T.2},
          (volume (tube δ T.1.1 T.1.2)).toReal⁻¹ * ∫ y in tube δ T.1.1 T.1.2, f y ≤ 1 :=
        fun T => tube_avg_le δ hδ _ _ T.2.1 f (fun y => by
          rw [abs_le]; constructor <;> linarith [hf1 y, hf0 y])
      have hge : 1 ≤ nikodymMaximal δ f x := by
        unfold nikodymMaximal
        let T0 : {T : E n × E n // ‖T.1‖ = 1 ∧ x ∈ tube δ T.1 T.2} :=
          ⟨(ω₀, x), hω₀, by
            refine ⟨?_, ?_⟩ <;> simp [hω₀, hδ.le]⟩
        refine le_trans ?_ (le_ciSup ⟨1, by rintro _ ⟨T, rfl⟩; exact hb T⟩ T0)
        show 1 ≤ (volume (tube δ ω₀ x)).toReal⁻¹ * ∫ y in tube δ ω₀ x, f y
        rw [tube_avg_eq δ hδ ω₀ x hω₀ f]
        intro y hy
        apply hfeq
        have h1 := tube_subset δ ω₀ x hω₀ hy
        rw [mem_closedBall, dist_eq_norm] at h1
        rw [mem_closedBall, dist_zero_right]
        have h2 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
        linarith
      rw [Real.enorm_eq_ofReal (by linarith)]
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
        _ ≤ _ := ENNReal.ofReal_le_ofReal hge
    _ ≤ _ := setLIntegral_le_lintegral _ _

end TaoBR

open TaoBR in
theorem solution : type_of% @TaoBR.nikodym_dev := @TaoBR.nikodym_dev
