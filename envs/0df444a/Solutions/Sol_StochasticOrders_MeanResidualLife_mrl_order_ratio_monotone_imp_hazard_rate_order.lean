-- Prove2me | solution 1 for StochasticOrders.MeanResidualLife.mrl_order_ratio_monotone_imp_hazard_rate_order
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:35:55.298987+00:00
-- url     : https://prove2.me/submissions/1f0c56c6-75b5-46de-8893-51995352d757

import Mathlib
import Definitions.Def_StochasticOrders_MeanResidualLife_mrl
import Definitions.Def_StochasticOrders_MeanResidualLife_MrlOrder
import Definitions.Def_StochasticOrders_MeanResidualLife_HazardRateOrder



namespace StochasticOrders.MeanResidualLife

open MeasureTheory Set Filter Topology

section Aux
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)

noncomputable def mrlFb (t : ℝ) : ℝ := (μ {ω | t < X ω}).toReal
noncomputable def mrlA (t : ℝ) : ℝ := ∫ ω in {ω | t < X ω}, (X ω - t) ∂μ

variable {μ X}

lemma mrlA_eq (hX : Measurable X) (t : ℝ) :
    mrlA μ X t = ∫ ω, max (X ω - t) 0 ∂μ := by
  unfold mrlA
  rw [← integral_indicator (measurableSet_lt measurable_const hX)]
  congr 1; funext ω
  by_cases h : t < X ω
  · simp [Set.indicator, h, le_of_lt (sub_pos.2 h)]
  · simp [Set.indicator, h]; linarith [not_lt.1 h]

lemma mrlFb_nonneg (t : ℝ) : 0 ≤ mrlFb μ X t := ENNReal.toReal_nonneg

lemma mrlFb_le_one (t : ℝ) : mrlFb μ X t ≤ 1 := by
  unfold mrlFb
  have := prob_le_one (μ := μ) (s := {ω | t < X ω})
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)

lemma mrlFb_anti : Antitone (mrlFb μ X) := by
  intro a b hab
  unfold mrlFb
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun ω (h : b < X ω) => (lt_of_le_of_lt hab h : a < X ω))

lemma mrlA_bounds (hX : Measurable X) (hXi : Integrable X μ) {t s : ℝ} (hts : t ≤ s) :
    (s - t) * mrlFb μ X s ≤ mrlA μ X t - mrlA μ X s ∧
      mrlA μ X t - mrlA μ X s ≤ (s - t) * mrlFb μ X t := by
  have hi : ∀ u : ℝ, Integrable (fun ω => max (X ω - u) 0) μ :=
    fun u => (hXi.sub (integrable_const u)).sup (integrable_zero _ _ _)
  rw [mrlA_eq hX, mrlA_eq hX, ← integral_sub (hi t) (hi s)]
  have hms : ∀ u : ℝ, MeasurableSet {ω | u < X ω} := fun u => measurableSet_lt measurable_const hX
  have e : ∀ u : ℝ, (s - t) * mrlFb μ X u =
      ∫ ω, Set.indicator {ω | u < X ω} (fun _ => s - t) ω ∂μ := by
    intro u
    rw [integral_indicator_const _ (hms u), smul_eq_mul, mul_comm]; rfl
  rw [e, e]
  constructor
  · apply integral_mono ((integrable_const _).indicator (hms s)) ((hi t).sub (hi s))
    intro ω
    by_cases h : s < X ω
    · simp only [Set.indicator, Set.mem_setOf_eq, h, if_true, Pi.sub_apply]
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · simp only [Set.indicator, Set.mem_setOf_eq, h, if_false, Pi.sub_apply]
      rw [max_eq_right (show X ω - s ≤ 0 by linarith [not_lt.1 h])]
      have := le_max_right (X ω - t) 0
      linarith
  · apply integral_mono ((hi t).sub (hi s)) ((integrable_const _).indicator (hms t))
    intro ω
    by_cases h : t < X ω
    · simp only [Set.indicator, Set.mem_setOf_eq, h, if_true, Pi.sub_apply]
      rcases le_or_gt (X ω) s with h2 | h2
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
      · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · simp only [Set.indicator, Set.mem_setOf_eq, h, if_false, Pi.sub_apply]
      rw [max_eq_right (by linarith [not_lt.1 h]), max_eq_right (by linarith [not_lt.1 h])]
      simp

lemma mrlFb_eq_cdf (hX : Measurable X) (t : ℝ) :
    mrlFb μ X t = 1 - ProbabilityTheory.cdf (μ.map X) t := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, Measure.map_apply hX measurableSet_Iic]
  unfold mrlFb
  have : {ω | t < X ω} = (X ⁻¹' Iic t)ᶜ := by ext ω; simp
  rw [this, prob_compl_eq_one_sub (hX measurableSet_Iic), ENNReal.toReal_sub_of_le prob_le_one
    ENNReal.one_ne_top]
  simp

lemma mrlFb_rc (hX : Measurable X) (t : ℝ) : ContinuousWithinAt (mrlFb μ X) (Ici t) t := by
  have : mrlFb μ X = fun u => 1 - ProbabilityTheory.cdf (μ.map X) u := funext (mrlFb_eq_cdf hX)
  rw [this]
  exact continuousWithinAt_const.sub ((ProbabilityTheory.cdf (μ.map X)).right_continuous t)

lemma mrlA_cont (hX : Measurable X) (hXi : Integrable X μ) : Continuous (mrlA μ X) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total a b with h | h
  · obtain ⟨h1, h2⟩ := mrlA_bounds hX hXi h
    have := mrlFb_nonneg (μ := μ) (X := X) b
    have := mrlFb_le_one (μ := μ) (X := X) a
    rw [abs_of_nonneg (by nlinarith), abs_of_nonpos (by linarith)]; nlinarith
  · obtain ⟨h1, h2⟩ := mrlA_bounds hX hXi h
    have := mrlFb_nonneg (μ := μ) (X := X) a
    have := mrlFb_le_one (μ := μ) (X := X) b
    rw [abs_of_nonpos (by nlinarith), abs_of_nonneg (by linarith)]; nlinarith

lemma mrlA_deriv (hX : Measurable X) (hXi : Integrable X μ) (t : ℝ) :
    HasDerivWithinAt (mrlA μ X) (-mrlFb μ X t) (Ici t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Ici t \ {t} = Ioi t := by ext u; simp [lt_iff_le_and_ne, eq_comm]
  rw [hset]
  have hlim : Tendsto (fun s => -mrlFb μ X s) (𝓝[>] t) (𝓝 (-mrlFb μ X t)) :=
    ((mrlFb_rc hX t).mono Ioi_subset_Ici_self).tendsto.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : t < s := hs
    obtain ⟨h1, h2⟩ := mrlA_bounds hX hXi hs'.le
    rw [slope_def_field, le_div_iff₀ (by linarith)]; nlinarith
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : t < s := hs
    obtain ⟨h1, h2⟩ := mrlA_bounds hX hXi hs'.le
    rw [slope_def_field, div_le_iff₀ (by linarith)]; nlinarith

lemma mrlA_zero (t : ℝ) (h : mrlFb μ X t = 0) : mrlA μ X t = 0 := by
  unfold mrlA
  apply setIntegral_measure_zero
  unfold mrlFb at h
  rcases (ENNReal.toReal_eq_zero_iff _).1 h with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

lemma mrlA_nonneg (hX : Measurable X) (t : ℝ) : 0 ≤ mrlA μ X t := by
  rw [mrlA_eq hX]
  exact integral_nonneg fun ω => le_max_right _ _

lemma mrlA_pos (hX : Measurable X) (hXi : Integrable X μ) (t : ℝ) (h : 0 < mrlFb μ X t) :
    0 < mrlA μ X t := by
  have hev : ∀ᶠ s in 𝓝[>] t, 0 < mrlFb μ X s :=
    ((mrlFb_rc hX t).mono Ioi_subset_Ici_self).tendsto.eventually (lt_mem_nhds h)
  obtain ⟨s, hs1, hs2⟩ := (hev.and self_mem_nhdsWithin).exists
  have hs2' : t < s := hs2
  obtain ⟨h1, _⟩ := mrlA_bounds hX hXi hs2'.le
  have := mrlA_nonneg (μ := μ) hX s
  have : 0 < (s - t) * mrlFb μ X s := mul_pos (by linarith) hs1
  linarith

lemma mrl_eq' (t : ℝ) : mrl μ X t = if 0 < mrlFb μ X t then mrlA μ X t / mrlFb μ X t else 0 := rfl

end Aux

theorem mrl_hr_core {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y ν)
    (hratio : MonotoneOn (fun t => mrl μ X t / mrl ν Y t) {t : ℝ | 0 < mrl ν Y t})
    (h : MrlOrder μ ν X Y) :
    HazardRateOrder μ ν X Y := by
  -- positivity facts
  have key : ∀ t, 0 < mrlFb μ X t →
      0 < mrl μ X t ∧ 0 < mrl ν Y t ∧ 0 < mrlFb ν Y t ∧ 0 < mrlA ν Y t ∧
      mrl μ X t = mrlA μ X t / mrlFb μ X t ∧ mrl ν Y t = mrlA ν Y t / mrlFb ν Y t := by
    intro t ht
    have hm : mrl μ X t = mrlA μ X t / mrlFb μ X t := by rw [mrl_eq', if_pos ht]
    have hmpos : 0 < mrl μ X t := by rw [hm]; exact div_pos (mrlA_pos hX hXi t ht) ht
    have hlpos : 0 < mrl ν Y t := lt_of_lt_of_le hmpos (h t)
    have hG : 0 < mrlFb ν Y t := by
      by_contra hc
      rw [mrl_eq', if_neg hc] at hlpos; exact lt_irrefl _ hlpos
    have hl : mrl ν Y t = mrlA ν Y t / mrlFb ν Y t := by rw [mrl_eq', if_pos hG]
    exact ⟨hmpos, hlpos, hG, mrlA_pos hY hYi t hG, hm, hl⟩
  intro x y hxy
  have hs1 : ∀ t, survival μ X t = ENNReal.ofReal (mrlFb μ X t) := by
    intro t
    unfold survival mrlFb
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hs2 : ∀ t, survival ν Y t = ENNReal.ofReal (mrlFb ν Y t) := by
    intro t
    unfold survival mrlFb
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hs1, hs1, hs2, hs2, ← ENNReal.ofReal_mul (mrlFb_nonneg _),
    ← ENNReal.ofReal_mul (mrlFb_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rcases (mrlFb_nonneg (μ := μ) (X := X) y).eq_or_lt with h0 | hy
  · rw [← h0, zero_mul]
    exact mul_nonneg (mrlFb_nonneg _) (mrlFb_nonneg _)
  -- A/B antitone on [x, y]
  have hpos : ∀ t ∈ Icc x y, 0 < mrlFb μ X t := fun t ht =>
    lt_of_lt_of_le hy (mrlFb_anti ht.2)
  have hAB : mrlA μ X y / mrlA ν Y y ≤ mrlA μ X x / mrlA ν Y x := by
    have := image_le_of_deriv_right_le_deriv_boundary
      (f := fun t => mrlA μ X t / mrlA ν Y t)
      (f' := fun t => ((-mrlFb μ X t) * mrlA ν Y t - mrlA μ X t * (-mrlFb ν Y t)) /
        (mrlA ν Y t) ^ 2)
      (a := x) (b := y) (B := fun _ => mrlA μ X x / mrlA ν Y x) (B' := fun _ => 0)
      ?_ ?_ le_rfl continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) ?_
      (show y ∈ Icc x y from ⟨hxy, le_rfl⟩)
    · exact this
    · apply ContinuousOn.div (mrlA_cont hX hXi).continuousOn (mrlA_cont hY hYi).continuousOn
      intro t ht; exact ((key t (hpos t ht)).2.2.2.1).ne'
    · intro t ht
      exact (mrlA_deriv hX hXi t).div (mrlA_deriv hY hYi t)
        ((key t (hpos t (Ico_subset_Icc_self ht))).2.2.2.1).ne'
    · intro t ht
      obtain ⟨hm, hl, hG, hB, em, el⟩ := key t (hpos t (Ico_subset_Icc_self ht))
      have hF := hpos t (Ico_subset_Icc_self ht)
      have hle := h t
      rw [em, el, div_le_div_iff₀ hF hG] at hle
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      nlinarith
  have hxpos := hpos x ⟨le_rfl, hxy⟩
  obtain ⟨hmx, hlx, hGx, hBx, emx, elx⟩ := key x hxpos
  obtain ⟨hmy, hly, hGy, hBy, emy, ely⟩ := key y hy
  have hr := hratio hlx hly hxy
  simp only at hr
  rw [div_le_div_iff₀ hlx hly] at hr
  rw [div_le_div_iff₀ hBy hBx] at hAB
  -- F = A / m, G = B / l
  have hFx : mrlFb μ X x = mrlA μ X x / mrl μ X x := by
    rw [emx]; field_simp [(mrlA_pos hX hXi x hxpos).ne']
  have hFy : mrlFb μ X y = mrlA μ X y / mrl μ X y := by
    rw [emy]; field_simp [(mrlA_pos hX hXi y hy).ne']
  have hGx' : mrlFb ν Y x = mrlA ν Y x / mrl ν Y x := by
    rw [elx]; field_simp [hBx.ne']
  have hGy' : mrlFb ν Y y = mrlA ν Y y / mrl ν Y y := by
    rw [ely]; field_simp [hBy.ne']
  rw [hFx, hFy, hGx', hGy', div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff₀ (mul_pos hmy hlx) (mul_pos hmx hly)]
  have hA0 := mrlA_nonneg (μ := μ) hX y
  have hB0 := mrlA_nonneg (μ := ν) hY x
  have hAx := mrlA_nonneg (μ := μ) hX x
  calc mrlA μ X y * mrlA ν Y x * (mrl μ X x * mrl ν Y y)
      ≤ mrlA μ X x * mrlA ν Y y * (mrl μ X x * mrl ν Y y) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    _ ≤ mrlA μ X x * mrlA ν Y y * (mrl μ X y * mrl ν Y x) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

end StochasticOrders.MeanResidualLife

open StochasticOrders.MeanResidualLife
open MeasureTheory StochasticOrders.MeanResidualLife

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXi : Integrable X μ) (hYi : Integrable Y ν)
    (hratio : MonotoneOn (fun t => mrl μ X t / mrl ν Y t) {t : ℝ | 0 < mrl ν Y t})
    (h : MrlOrder μ ν X Y) :
    HazardRateOrder μ ν X Y := by
  exact mrl_hr_core μ ν X Y hX hY hXi hYi hratio h
