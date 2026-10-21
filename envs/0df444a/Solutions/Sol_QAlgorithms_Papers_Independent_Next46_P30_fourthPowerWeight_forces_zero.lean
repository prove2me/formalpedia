-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P30.fourthPowerWeight_forces_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T14:35:55.772949+00:00
-- url     : https://prove2.me/submissions/18bc126f-4f2b-460b-96b4-1ff978e811b3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P30
noncomputable section

open MeasureTheory Filter Topology Metric

open QAlgorithms.Papers.Independent.Next46.P30

open scoped ENNReal

lemma g61b_leb {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hfin : ∫⁻ y, f y ≠ ∞) :
    ∀ᵐ x : ℝ, Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, f y) / volume (closedBall x r))
      (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [(IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_lintegral_div
    hf.aemeasurable hfin] with x hx
  refine hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt (volume : Measure ℝ)
    (fun _ => x) (fun r => r) tendsto_id ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [one_mul, mem_closedBall, dist_self]
  exact le_of_lt hr

lemma g61b_w8 (lam t r : ℝ) (ht : t ≠ lam) (hr : 0 < r) (htr : |t - lam| ≤ r) :
    (r ^ 2)⁻¹ ≤ ((singularWeight lam t) ^ 4) ^ 2 := by
  have hpos : 0 < |t - lam| := abs_pos.2 (sub_ne_zero.2 ht)
  have h4 : (singularWeight lam t) ^ 4 = |t - lam|⁻¹ := by
    simp only [singularWeight, ht, if_false]
    rw [Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num [Real.rpow_neg_one]
  rw [h4, inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le htr 2)

theorem solution (xi : HilbertSpace)
    (hweight : ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      MemLp (fun t : ℝ => (((singularWeight lam t) ^ 4 : ℝ) : ℂ) * xi t)
        2 intervalMeasure) :
    xi = 0 := by
  set S := Set.Icc (0 : ℝ) 1 with hS
  have hSm : MeasurableSet S := measurableSet_Icc
  let f : ℝ → ℝ≥0∞ := S.indicator (fun t => ENNReal.ofReal (‖xi t‖ ^ 2))
  have hxm : Measurable (fun t => ENNReal.ofReal (‖xi t‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((Lp.stronglyMeasurable xi).measurable.norm.pow_const 2)
  have hfm : Measurable f := hxm.indicator hSm
  have hint : Integrable (fun t => ‖xi t‖ ^ 2) intervalMeasure :=
    (Lp.memLp xi).integrable_norm_pow (by norm_num)
  have hfin : ∫⁻ y, f y ≠ ∞ := by
    rw [lintegral_indicator hSm]
    exact (hint.lintegral_lt_top).ne
  have hae := g61b_leb hfm hfin
  have h0 : ∀ᵐ t ∂intervalMeasure, xi t = 0 := by
    rw [ae_iff]
    change (volume.restrict S) {a | ¬ xi a = 0} = 0
    rw [Measure.restrict_apply' hSm]
    by_contra hne
    have hex : ∃ lam, (lam ∈ {a | ¬ xi a = 0} ∩ S) ∧
        Tendsto (fun r : ℝ => (∫⁻ y in closedBall lam r, f y) / volume (closedBall lam r))
          (𝓝[>] 0) (𝓝 (f lam)) := by
      by_contra hno
      push Not at hno
      apply hne
      apply measure_mono_null _ (ae_iff.1 hae)
      intro a ha hc
      exact hno a ha hc
    obtain ⟨lam, ⟨hxl, hlS⟩, hlim⟩ := hex
    have hc : f lam = ENNReal.ofReal (‖xi lam‖ ^ 2) := Set.indicator_of_mem hlS _
    have hcpos : f lam ≠ 0 := by
      rw [hc]; simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : xi lam ≠ 0 := hxl
      positivity
    have hcfin : f lam ≠ ∞ := by rw [hc]; exact ENNReal.ofReal_ne_top
    set c := f lam
    -- the weighted integral is finite
    have hW := (hweight lam hlS).integrable_norm_pow (p := 2) (by norm_num)
    set T := ∫⁻ t, ENNReal.ofReal (‖(((singularWeight lam t) ^ 4 : ℝ) : ℂ) * xi t‖ ^ 2)
      ∂intervalMeasure with hT
    have hTfin : T < ∞ := hW.lintegral_lt_top
    -- lower bound
    have hlow : ∀ r : ℝ, 0 < r →
        ENNReal.ofReal ((r ^ 2)⁻¹) * ∫⁻ y in closedBall lam r, f y ≤ T := by
      intro r hr
      have hTe : T = ∫⁻ t, S.indicator (fun t => ENNReal.ofReal
          (‖(((singularWeight lam t) ^ 4 : ℝ) : ℂ) * xi t‖ ^ 2)) t :=
        (lintegral_indicator hSm _).symm
      rw [hTe, ← lintegral_const_mul _ hfm]
      refine le_trans ?_ (setLIntegral_le_lintegral (closedBall lam r) _)
      have hne_ae : ∀ᵐ t ∂(volume.restrict (closedBall lam r)), t ≠ lam := by
        apply ae_restrict_of_ae
        have : (volume : Measure ℝ) {lam} = 0 := Real.volume_singleton
        rw [ae_iff]; simpa using this
      have hmem : ∀ᵐ t ∂(volume.restrict (closedBall lam r)), t ∈ closedBall lam r :=
        ae_restrict_mem measurableSet_closedBall
      refine lintegral_mono_ae ?_
      filter_upwards [hne_ae, hmem] with t ht htm
      by_cases htS : t ∈ S
      · simp only [f, Set.indicator_of_mem htS]
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        have := g61b_w8 lam t r ht hr (by rw [mem_closedBall, Real.dist_eq] at htm; exact htm)
        exact mul_le_mul_of_nonneg_right this (by positivity)
      · simp [f, Set.indicator_of_notMem htS]
    -- eventually the average exceeds c/2
    have hev1 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        c / 2 < (∫⁻ y in closedBall lam r, f y) / volume (closedBall lam r) :=
      hlim (Ioi_mem_nhds (ENNReal.half_lt_self hcpos hcfin))
    have htend : Tendsto (fun r : ℝ => c / 2 * ENNReal.ofReal (2 / r)) (𝓝[>] 0) (𝓝 ∞) := by
      have h1 : Tendsto (fun r : ℝ => ENNReal.ofReal (2 / r)) (𝓝[>] 0) (𝓝 ∞) := by
        apply ENNReal.tendsto_ofReal_atTop.comp
        exact (tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num : (0:ℝ) < 2)).congr
          (fun r => by simp [div_eq_mul_inv])
      have h2 := ENNReal.Tendsto.const_mul (a := c / 2) h1 (Or.inl (by simp))
      rwa [ENNReal.mul_top (ENNReal.half_pos hcpos).ne'] at h2
    have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), T < c / 2 * ENNReal.ofReal (2 / r) :=
      htend (Ioi_mem_nhds hTfin)
    obtain ⟨r, ⟨h1, h2⟩, hr⟩ := ((hev1.and hev2).and self_mem_nhdsWithin).exists
    have hr : (0 : ℝ) < r := hr
    rw [Real.volume_closedBall] at h1
    have h1' : c / 2 * ENNReal.ofReal (2 * r) < ∫⁻ y in closedBall lam r, f y := by
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by simp; positivity)) (Or.inl ENNReal.ofReal_ne_top)]
        at h1
      exact h1
    have := hlow r hr
    have key : c / 2 * ENNReal.ofReal (2 / r) =
        ENNReal.ofReal ((r ^ 2)⁻¹) * (c / 2 * ENNReal.ofReal (2 * r)) := by
      rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
      congr 2; field_simp
    have : c / 2 * ENNReal.ofReal (2 / r) < T := by
      rw [key]
      calc ENNReal.ofReal ((r ^ 2)⁻¹) * (c / 2 * ENNReal.ofReal (2 * r))
          < ENNReal.ofReal ((r ^ 2)⁻¹) * ∫⁻ y in closedBall lam r, f y :=
            (ENNReal.mul_lt_mul_iff_right (by simp; positivity) ENNReal.ofReal_ne_top).2 h1'
        _ ≤ T := this
    exact absurd h2 (not_lt.2 this.le)
  apply Lp.ext
  filter_upwards [h0, Lp.coeFn_zero ℂ 2 intervalMeasure] with t ht hz
  rw [ht, hz]; rfl
