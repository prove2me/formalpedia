-- Prove2me | solution 1 for RetailerMarketplace.Entry.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T17:00:02.09305+00:00
-- url     : https://prove2.me/submissions/1fd99ccc-2407-4983-9a24-44a405324e83

import Definitions.Def_RetailerMarketplace_Entry_Model

open MeasureTheory Set Filter Topology

namespace RetailerMarketplace.Entry

lemma rm_G_eq_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    G μ = ⇑(ProbabilityTheory.cdf μ) := by
  funext x
  rw [ProbabilityTheory.cdf_eq_real]
  rfl

lemma rm_G_continuous (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsing : ∀ x, μ {x} = 0) :
    Continuous (G μ) := by
  rw [rm_G_eq_cdf]
  have hmono : Monotone ⇑(ProbabilityTheory.cdf μ) := (ProbabilityTheory.cdf μ).mono
  refine continuous_iff_continuousAt.2 fun x => ?_
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hr : Function.rightLim (⇑(ProbabilityTheory.cdf μ)) x = ProbabilityTheory.cdf μ x :=
    ((ProbabilityTheory.cdf μ).right_continuous x).rightLim_eq
  have hl : Function.leftLim (⇑(ProbabilityTheory.cdf μ)) x = ProbabilityTheory.cdf μ x := by
    have h1 := (ProbabilityTheory.cdf μ).measure_singleton x
    rw [ProbabilityTheory.measure_cdf, hsing x] at h1
    have h2 : ProbabilityTheory.cdf μ x - Function.leftLim (⇑(ProbabilityTheory.cdf μ)) x ≤ 0 :=
      ENNReal.ofReal_eq_zero.1 h1.symm
    have h3 : Function.leftLim (⇑(ProbabilityTheory.cdf μ)) x ≤ ProbabilityTheory.cdf μ x :=
      hmono.leftLim_le le_rfl
    linarith
  rw [hl, hr]

lemma rm_bathtub_core {μ : Measure ℝ} [IsFiniteMeasure μ] {h : ℝ → ℝ} (hh : Integrable h μ)
    {U A : Set ℝ} (hU : MeasurableSet U) (hA : MeasurableSet A) {t : ℝ} (ht : 0 ≤ t)
    (h1 : ∀ᵐ v ∂μ, v ∈ U → t < h v) (h2 : ∀ᵐ v ∂μ, v ∉ U → h v < t) (hμ : μ A ≤ μ U) :
    ∫ v in A, h v ∂μ ≤ ∫ v in U, h v ∂μ ∧
      (∫ v in U, h v ∂μ ≤ ∫ v in A, h v ∂μ → A =ᵐ[μ] U) := by
  have eA := integral_inter_add_sdiff hU (hh.integrableOn (s := A))
  have eU := integral_inter_add_sdiff hA (hh.integrableOn (s := U))
  rw [Set.inter_comm U A] at eU
  have hUA : MeasurableSet (U \ A) := hU.diff hA
  have hAU : MeasurableSet (A \ U) := hA.diff hU
  have hXi : Integrable (fun v => h v - t) (μ.restrict (U \ A)) :=
    hh.integrableOn.sub (integrable_const t)
  have hYi : Integrable (fun v => t - h v) (μ.restrict (A \ U)) :=
    (integrable_const t).sub hh.integrableOn
  have hXpos : ∀ᵐ v ∂μ.restrict (U \ A), 0 < h v - t := by
    rw [ae_restrict_iff' hUA]
    filter_upwards [h1] with v hv hvm
    exact sub_pos.2 (hv hvm.1)
  have hYpos : ∀ᵐ v ∂μ.restrict (A \ U), 0 < t - h v := by
    rw [ae_restrict_iff' hAU]
    filter_upwards [h2] with v hv hvm
    exact sub_pos.2 (hv hvm.2)
  have hXnn : 0 ≤ᵐ[μ.restrict (U \ A)] (fun v => h v - t) := by
    filter_upwards [hXpos] with v hv
    exact hv.le
  have hYnn : 0 ≤ᵐ[μ.restrict (A \ U)] (fun v => t - h v) := by
    filter_upwards [hYpos] with v hv
    exact hv.le
  have hX0 : 0 ≤ ∫ v in U \ A, (h v - t) ∂μ := integral_nonneg_of_ae hXnn
  have hY0 : 0 ≤ ∫ v in A \ U, (t - h v) ∂μ := integral_nonneg_of_ae hYnn
  have hXe : ∫ v in U \ A, (h v - t) ∂μ = ∫ v in U \ A, h v ∂μ - μ.real (U \ A) * t := by
    rw [integral_sub hh.integrableOn (integrable_const t), setIntegral_const, smul_eq_mul]
  have hYe : ∫ v in A \ U, (t - h v) ∂μ = μ.real (A \ U) * t - ∫ v in A \ U, h v ∂μ := by
    rw [integral_sub (integrable_const t) hh.integrableOn, setIntegral_const, smul_eq_mul]
  have hmA : μ.real (A ∩ U) + μ.real (A \ U) = μ.real A := by
    simp only [measureReal_def]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_inter_add_sdiff A hU]
  have hmU : μ.real (U ∩ A) + μ.real (U \ A) = μ.real U := by
    simp only [measureReal_def]
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_inter_add_sdiff U hA]
  rw [Set.inter_comm U A] at hmU
  have hmono : μ.real A ≤ μ.real U := by
    simp only [measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hμ
  have hmass : μ.real (A \ U) ≤ μ.real (U \ A) := by linarith
  have htm := mul_le_mul_of_nonneg_right hmass ht
  refine ⟨by linarith, fun hle => ?_⟩
  have hXz : ∫ v in U \ A, (h v - t) ∂μ = 0 := by linarith
  have hYz : ∫ v in A \ U, (t - h v) ∂μ = 0 := by linarith
  have hX' := (integral_eq_zero_iff_of_nonneg_ae hXnn hXi).1 hXz
  have hY' := (integral_eq_zero_iff_of_nonneg_ae hYnn hYi).1 hYz
  have hfX : ∀ᵐ v ∂μ.restrict (U \ A), False := by
    filter_upwards [hXpos, hX'] with v hv1 hv2
    simp only [Pi.zero_apply] at hv2
    linarith
  have hfY : ∀ᵐ v ∂μ.restrict (A \ U), False := by
    filter_upwards [hYpos, hY'] with v hv1 hv2
    simp only [Pi.zero_apply] at hv2
    linarith
  rw [Filter.eventually_false_iff_eq_bot, ae_eq_bot, Measure.restrict_eq_zero] at hfX hfY
  exact ae_eq_set.2 ⟨hfY, hfX⟩

lemma rm_optimal_of_bathtub {μ : Measure ℝ} [IsProbabilityMeasure μ] {c f lam k : ℝ}
    {h : ℝ → ℝ} {C : ℝ}
    (hprof : ∀ A, MeasurableSet A → profitM μ c f lam A = C + ∫ v in A, h v ∂μ)
    (hh : Integrable h μ) {U : Set ℝ} (hU : MeasurableSet U) (hUk : μ U = ENNReal.ofReal k)
    {t : ℝ} (ht : 0 ≤ t) (h1 : ∀ᵐ v ∂μ, v ∈ U → t < h v) (h2 : ∀ᵐ v ∂μ, v ∉ U → h v < t) :
    IsOptimalAlloc μ c f lam k U ∧ ∀ A, IsOptimalAlloc μ c f lam k A → A =ᵐ[μ] U := by
  have hadm : Admissible μ k U := ⟨hU, hUk.le⟩
  refine ⟨⟨hadm, fun B hB => ?_⟩, fun A hA => ?_⟩
  · rw [hprof B hB.1, hprof U hU]
    have := (rm_bathtub_core hh hU hB.1 ht h1 h2 (hB.2.trans hUk.ge)).1
    linarith
  · have hle := hA.2 U hadm
    rw [hprof U hU, hprof A hA.1.1] at hle
    exact (rm_bathtub_core hh hU hA.1.1 ht h1 h2 (hA.1.2.trans hUk.ge)).2 (by linarith)

lemma rm_optimal_zero {μ : Measure ℝ} [IsProbabilityMeasure μ] {c f lam : ℝ}
    {h : ℝ → ℝ} {C : ℝ}
    (hprof : ∀ A, MeasurableSet A → profitM μ c f lam A = C + ∫ v in A, h v ∂μ) :
    IsOptimalAlloc μ c f lam 0 ∅ ∧
      ∀ A, IsOptimalAlloc μ c f lam 0 A → A =ᵐ[μ] (∅ : Set ℝ) := by
  have hz : ∀ B, Admissible μ 0 B → μ B = 0 := fun B hB => by simpa using hB.2
  have hadm : Admissible μ 0 ∅ := ⟨MeasurableSet.empty, by simp⟩
  refine ⟨⟨hadm, fun B hB => ?_⟩, fun A hA => ?_⟩
  · rw [hprof B hB.1, hprof ∅ MeasurableSet.empty, Measure.restrict_eq_zero.2 (hz B hB)]
    simp
  · exact ae_eq_empty.2 (hz A hA.1)

lemma rm_real_Ici (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsing : ∀ x, μ {x} = 0) (x : ℝ) :
    (μ (Ici x)).toReal = 1 - G μ x := by
  have : NullSingletonClass μ := ⟨hsing⟩
  rw [← measure_congr (Ioi_ae_eq_Ici (μ := μ) (a := x))]
  have h := measure_add_measure_compl (μ := μ) (measurableSet_Iic (a := x))
  rw [compl_Iic, measure_univ] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h2
  unfold G
  linarith

lemma rm_real_Ico (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsing : ∀ x, μ {x} = 0) {a b : ℝ}
    (hab : a ≤ b) : (μ (Ico a b)).toReal = G μ b - G μ a := by
  have : NullSingletonClass μ := ⟨hsing⟩
  rw [measure_congr (Ico_ae_eq_Ioc (μ := μ) (a := a) (b := b))]
  have h := measure_union (μ := μ) (s₁ := Iic a) (s₂ := Ioc a b)
    (Set.disjoint_left.2 fun x hx1 hx2 => by simp only [mem_Iic, mem_Ioc] at hx1 hx2; linarith)
    measurableSet_Ioc
  rw [Iic_union_Ioc_eq_Iic hab] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  unfold G
  linarith

theorem proposition_2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam k : ℝ) (hc : 0 < c)
    (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hk : k ∈ Set.Icc (0 : ℝ) 1) (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume)
    (hint : Integrable (fun v : ℝ => v) μ)
    (hfull : ∀ a b : ℝ, c ≤ a → a < b → 0 < μ (Set.Ioo a b)) :
    ∃ k₀ ∈ Set.Icc (0 : ℝ) 1, k₀ = kbar μ c f lam ∧
      (k ≤ k₀ →
        ∃ U : Set ℝ,
          ((k = 0 ∧ U = ∅) ∨
            ∃ vK : ℝ, vT c f ≤ vK ∧ 1 - G μ vK = k ∧ U = Set.Ici vK) ∧
          IsOptimalAlloc μ c f lam k U ∧
          ∀ A : Set ℝ, IsOptimalAlloc μ c f lam k A → A =ᵐ[μ] U) ∧
      (k₀ < k →
        ∃ vL vH : ℝ, c ≤ vL ∧ vL ≤ vT c f ∧ vT c f ≤ vH ∧
          piSBM c vL = dPi c f lam vH ∧
          (1 - G μ vH) + (G μ (vT c f) - G μ vL) = k ∧
          IsOptimalAlloc μ c f lam k (Set.Ico vL (vT c f) ∪ Set.Ici vH) ∧
          ∀ A : Set ℝ, IsOptimalAlloc μ c f lam k A →
            A =ᵐ[μ] (Set.Ico vL (vT c f) ∪ Set.Ici vH : Set ℝ)) := by
  have hf0 : 0 ≤ f := hf.1
  have hf1 : f < 1 := hf.2
  have hl1 : 1 / 2 ≤ lam := hlam.1
  have hl2 : lam ≤ 1 := hlam.2
  have h1f : 0 < 1 - f := by linarith
  have hE : 0 < lam - f * (1 - lam) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * lam - 1) hf0,
      mul_pos h1f (by linarith : (0:ℝ) < lam)]
  have hD : 0 < 1 - f * (1 - lam) := by
    nlinarith [mul_nonneg h1f.le (by linarith : (0:ℝ) ≤ 1 - lam)]
  have hvtc : c ≤ vT c f := by
    rw [vT, le_div_iff₀ h1f]; nlinarith [mul_nonneg hc.le hf0]
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = (1 - f) * (lam - f * (1 - lam)) / (1 - f * (1 - lam)) :=
    ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; exact div_pos (mul_pos h1f hE) hD
  have hdPi : ∀ v, dPi c f lam v = a * (v - vT c f) := by
    intro v
    simp only [dPi, piSBMT_M, piSBT_M, pbarT, ha_def, vT]
    have hD0 := hD
    generalize hDg : 1 - f * (1 - lam) = D at hD0 ⊢
    have hD' : D ≠ 0 := hD0.ne'
    have h1f' : 1 - f ≠ 0 := h1f.ne'
    field_simp
    rw [← hDg]
    ring
  have hstar : a * (vStar c f lam - vT c f) = vT c f - c := by
    simp only [vStar, ha_def, vT]
    field_simp
    ring
  have hvs_ge : vT c f ≤ vStar c f lam := by
    by_contra hcon
    push_neg at hcon
    have : a * (vStar c f lam - vT c f) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
    linarith
  have hmp : mp c f = Ici (vT c f) := by
    ext v
    simp only [mp, mem_setOf_eq, mem_Ici, vT]
    rw [div_le_iff₀ h1f]
  have hsing : ∀ x, μ {x} = 0 := fun x => hac Real.volume_singleton
  have hG : Continuous (G μ) := rm_G_continuous μ hsing
  have hae_c : ∀ᵐ v ∂μ, c ≤ v := by
    rw [ae_iff]
    have : {v : ℝ | ¬ c ≤ v} = Iio c := by ext; simp
    rw [this]; exact hsupp
  have hae_ne : ∀ x, ∀ᵐ v ∂μ, v ≠ x := by
    intro x
    rw [ae_iff]
    have : {v : ℝ | ¬ v ≠ x} = {x} := by ext; simp
    rw [this]; exact hsing x
  have hGc : G μ c = 0 := by
    have : μ (Iic c) = 0 := by
      rw [← Iio_union_right]
      exact measure_union_null hsupp (hsing c)
    simp [G, this]
  have hG01 : ∀ x, 0 ≤ G μ x ∧ G μ x ≤ 1 := by
    intro x
    rw [rm_G_eq_cdf]
    exact ⟨ProbabilityTheory.cdf_nonneg μ x, ProbabilityTheory.cdf_le_one μ x⟩
  have hGmono : Monotone (G μ) := by
    rw [rm_G_eq_cdf]; exact (ProbabilityTheory.cdf μ).mono
  -- the marginal-profit function
  obtain ⟨h, hdef⟩ : ∃ h : ℝ → ℝ, h = fun v => (Ici (vT c f)).indicator
      (fun v => a * (v - vT c f)) v + (Ici (vT c f))ᶜ.indicator (fun v => v - c) v := ⟨_, rfl⟩
  have hhA : ∀ v, vT c f ≤ v → h v = a * (v - vT c f) := by
    intro v hv; rw [hdef]; simp [Set.indicator, hv]
  have hhB : ∀ v, v < vT c f → h v = v - c := by
    intro v hv; rw [hdef]; simp [Set.indicator, hv, not_le.2 hv]
  have hh : Integrable h μ := by
    rw [hdef]
    exact (((hint.sub (integrable_const (vT c f))).const_mul a).indicator measurableSet_Ici).add
      ((hint.sub (integrable_const c)).indicator measurableSet_Ici.compl)
  have i2 : Integrable (fun v => piSBT_M f v) μ := by
    simp only [piSBT_M]; exact hint.const_mul f
  have i1 : Integrable (fun v => piSBMT_M c f lam v) μ := by
    have : (fun v => piSBMT_M c f lam v) = fun v => a * (v - vT c f) + f * v := by
      funext v
      have := hdPi v
      simp only [dPi, piSBT_M] at this
      linarith
    rw [this]
    exact ((hint.sub (integrable_const _)).const_mul a).add (hint.const_mul f)
  have hprof : ∀ A, MeasurableSet A → profitM μ c f lam A =
      (∫ v in Ici (vT c f), piSBT_M f v ∂μ) + ∫ v in A, h v ∂μ := by
    intro A hA
    have hS : MeasurableSet (Ici (vT c f)) := measurableSet_Ici
    unfold profitM
    rw [hmp]
    have e1 := integral_inter_add_sdiff hS (hh.integrableOn (s := A))
    have e2 : ∫ v in A ∩ Ici (vT c f), h v ∂μ = ∫ v in A ∩ Ici (vT c f), dPi c f lam v ∂μ :=
      setIntegral_congr_fun (hA.inter hS) (fun v hv => by rw [hhA v hv.2, hdPi])
    have e3 : ∫ v in A \ Ici (vT c f), h v ∂μ = ∫ v in A \ Ici (vT c f), piSBM c v ∂μ :=
      setIntegral_congr_fun (hA.diff hS)
        (fun v hv => by rw [hhB v (not_le.1 hv.2)]; rfl)
    have e4 : ∫ v in A ∩ Ici (vT c f), dPi c f lam v ∂μ =
        ∫ v in A ∩ Ici (vT c f), piSBMT_M c f lam v ∂μ
          - ∫ v in A ∩ Ici (vT c f), piSBT_M f v ∂μ := by
      simp only [dPi]; exact integral_sub i1.integrableOn i2.integrableOn
    have e5 := integral_inter_add_sdiff hA (i2.integrableOn (s := Ici (vT c f)))
    rw [Set.inter_comm (Ici (vT c f)) A] at e5
    linarith
  refine ⟨kbar μ c f lam, ⟨?_, ?_⟩, rfl, ?_, ?_⟩
  · unfold kbar; linarith [(hG01 (vStar c f lam)).2]
  · unfold kbar; linarith [(hG01 (vStar c f lam)).1]
  · -- Mode I
    intro hk0
    rcases eq_or_lt_of_le hk.1 with hk00 | hkpos
    · subst hk00
      exact ⟨∅, Or.inl ⟨rfl, rfl⟩, rm_optimal_zero hprof⟩
    · have hGtop : Tendsto (G μ) atTop (𝓝 1) := by
        rw [rm_G_eq_cdf]; exact ProbabilityTheory.tendsto_cdf_atTop μ
      obtain ⟨R, hR⟩ := (hGtop.eventually (lt_mem_nhds (by linarith : 1 - k < 1))).exists
      have hR' : 1 - k ≤ G μ (max R (vStar c f lam)) :=
        hR.le.trans (hGmono (le_max_left _ _))
      have hstarle : G μ (vStar c f lam) ≤ 1 - k := by unfold kbar at hk0; linarith
      obtain ⟨vK, hvK, hGvK⟩ := intermediate_value_Icc (le_max_right R (vStar c f lam))
        hG.continuousOn ⟨hstarle, hR'⟩
      have hvK1 : vStar c f lam ≤ vK := hvK.1
      have hvTvK : vT c f ≤ vK := hvs_ge.trans hvK1
      refine ⟨Ici vK, Or.inr ⟨vK, hvTvK, by linarith, rfl⟩, ?_⟩
      have hUk : μ (Ici vK) = ENNReal.ofReal k := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ (Ici vK)), rm_real_Ici μ hsing vK, hGvK]
        ring_nf
      refine rm_optimal_of_bathtub hprof hh measurableSet_Ici hUk (t := a * (vK - vT c f))
        (mul_nonneg ha.le (by linarith)) ?_ ?_
      · filter_upwards [hae_ne vK] with v hne hv
        have hv' : vK < v := lt_of_le_of_ne (mem_Ici.1 hv) hne.symm
        rw [hhA v (by linarith)]
        exact mul_lt_mul_of_pos_left (by linarith) ha
      · filter_upwards [hae_c] with v hcv hv
        have hv' : v < vK := not_le.1 hv
        rcases le_or_gt (vT c f) v with hvt | hvt
        · rw [hhA v hvt]
          exact mul_lt_mul_of_pos_left (by linarith) ha
        · rw [hhB v hvt]
          have : a * (vStar c f lam - vT c f) ≤ a * (vK - vT c f) :=
            mul_le_mul_of_nonneg_left (by linarith) ha.le
          linarith
  · -- Mode II
    intro hk0
    have hm : Continuous fun s : ℝ =>
        1 - G μ (vT c f + s / a) + G μ (vT c f) - G μ (c + s) := by
      have h1 : Continuous fun s : ℝ => G μ (vT c f + s / a) :=
        hG.comp (continuous_const.add (continuous_id.div_const a))
      have h2 : Continuous fun s : ℝ => G μ (c + s) :=
        hG.comp (continuous_const.add continuous_id)
      exact ((continuous_const.sub h1).add continuous_const).sub h2
    have hvs : vT c f + (vT c f - c) / a = vStar c f lam := by
      rw [← hstar, mul_div_cancel_left₀ _ ha.ne']; ring
    have hm0 : 1 - G μ (vT c f + 0 / a) + G μ (vT c f) - G μ (c + 0) = 1 := by
      simp [hGc]
    have hm1 : 1 - G μ (vT c f + (vT c f - c) / a) + G μ (vT c f) - G μ (c + (vT c f - c))
        = kbar μ c f lam := by
      rw [hvs, kbar]; ring_nf
    obtain ⟨s, hs, hms⟩ := intermediate_value_Icc' (sub_nonneg.2 hvtc) hm.continuousOn
      (⟨by rw [hm1]; exact hk0.le, by rw [hm0]; exact hk.2⟩ :
        k ∈ Icc (1 - G μ (vT c f + (vT c f - c) / a) + G μ (vT c f) - G μ (c + (vT c f - c)))
          (1 - G μ (vT c f + 0 / a) + G μ (vT c f) - G μ (c + 0)))
    simp only at hms
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ vT c f - c := hs.2
    have hsa : 0 ≤ s / a := div_nonneg hs0 ha.le
    have hvH : a * (vT c f + s / a - vT c f) = s := by
      rw [add_sub_cancel_left, mul_div_cancel₀ _ ha.ne']
    refine ⟨c + s, vT c f + s / a, by linarith, by linarith, by linarith, ?_, by linarith, ?_⟩
    · rw [hdPi, hvH, piSBM]; ring
    have hUk : μ (Ico (c + s) (vT c f) ∪ Ici (vT c f + s / a)) = ENNReal.ofReal k := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      congr 1
      rw [measure_union (Set.disjoint_left.2 fun x hx1 hx2 => by
          simp only [mem_Ico, mem_Ici] at hx1 hx2; linarith) measurableSet_Ici,
        ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
        rm_real_Ico μ hsing (by linarith), rm_real_Ici μ hsing]
      linarith
    refine rm_optimal_of_bathtub hprof hh (measurableSet_Ico.union measurableSet_Ici) hUk
      (t := s) hs0 ?_ ?_
    · filter_upwards [hae_ne (c + s), hae_ne (vT c f + s / a)] with v hne1 hne2 hv
      rcases hv with hv | hv
      · have hv1 : c + s < v := lt_of_le_of_ne hv.1 hne1.symm
        rw [hhB v hv.2]; linarith
      · have hv1 : vT c f + s / a < v := lt_of_le_of_ne (mem_Ici.1 hv) hne2.symm
        rw [hhA v (by linarith)]
        have : a * (vT c f + s / a - vT c f) < a * (v - vT c f) :=
          mul_lt_mul_of_pos_left (by linarith) ha
        linarith
    · filter_upwards [hae_c] with v hcv hv
      simp only [mem_union, mem_Ico, mem_Ici, not_or, not_and, not_le, not_lt] at hv
      rcases le_or_gt (vT c f) v with hvt | hvt
      · rw [hhA v hvt]
        have : a * (v - vT c f) < a * (vT c f + s / a - vT c f) :=
          mul_lt_mul_of_pos_left (by linarith [hv.2]) ha
        linarith
      · rw [hhB v hvt]
        have : v < c + s := by
          by_contra hcon
          push_neg at hcon
          linarith [hv.1 hcon]
        linarith

end RetailerMarketplace.Entry


-- Platform entry point: restates the target verbatim.
namespace RetailerMarketplace.Entry

/-- Proposition 2: there is a capacity threshold `k̲ ∈ [0, 1]` (namely `1 - G(v*)`) such that M's
optimal capacity allocations (unique up to `μ`-null sets) are
1. (Mode I, `k ≤ k̲`) the top products `[v_K, ∞)` with `1 - G(v_K) = k` and `v_K ≥ v_T`, so that
   `[v_T, v_K)` is SBT and `[v_K, ∞)` is SBMT (no product at all when `k = 0`);
2. (Mode II, `k > k̲`) `[v_L, v_T) ∪ [v_H, ∞)` with `c ≤ v_L ≤ v_T ≤ v_H`, where `v_L, v_H` equalize
   `π_M^SBM(v_L) = Δπ_M^{SBMT-SBT}(v_H)` and use all capacity, so that `[v_L, v_T)` is SBM,
   `[v_T, v_H)` is SBT and `[v_H, ∞)` is SBMT. -/
theorem _root_.solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam k : ℝ) (hc : 0 < c)
    (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hk : k ∈ Set.Icc (0 : ℝ) 1) (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume)
    (hint : Integrable (fun v : ℝ => v) μ)
    (hfull : ∀ a b : ℝ, c ≤ a → a < b → 0 < μ (Set.Ioo a b)) :
    ∃ k₀ ∈ Set.Icc (0 : ℝ) 1, k₀ = kbar μ c f lam ∧
      (k ≤ k₀ →
        ∃ U : Set ℝ,
          ((k = 0 ∧ U = ∅) ∨
            ∃ vK : ℝ, vT c f ≤ vK ∧ 1 - G μ vK = k ∧ U = Set.Ici vK) ∧
          IsOptimalAlloc μ c f lam k U ∧
          ∀ A : Set ℝ, IsOptimalAlloc μ c f lam k A → A =ᵐ[μ] U) ∧
      (k₀ < k →
        ∃ vL vH : ℝ, c ≤ vL ∧ vL ≤ vT c f ∧ vT c f ≤ vH ∧
          piSBM c vL = dPi c f lam vH ∧
          (1 - G μ vH) + (G μ (vT c f) - G μ vL) = k ∧
          IsOptimalAlloc μ c f lam k (Set.Ico vL (vT c f) ∪ Set.Ici vH) ∧
          ∀ A : Set ℝ, IsOptimalAlloc μ c f lam k A →
            A =ᵐ[μ] (Set.Ico vL (vT c f) ∪ Set.Ici vH : Set ℝ)) := by
  apply @RetailerMarketplace.Entry.proposition_2 <;> assumption

end RetailerMarketplace.Entry
