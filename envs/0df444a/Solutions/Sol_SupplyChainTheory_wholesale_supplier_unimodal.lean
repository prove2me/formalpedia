-- Prove2me | solution 1 for SupplyChainTheory.wholesale_supplier_unimodal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:04:54.145985+00:00
-- url     : https://prove2.me/submissions/c52f5371-22cd-4642-a534-a96574bd366d

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts

open MeasureTheory ProbabilityTheory

namespace SupplyChainTheory

lemma sc_int_min (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (Q : ℝ) : Integrable (fun d => min Q d) D := by
  refine Integrable.mono' ((integrable_const |Q|).add hD.abs)
    (measurable_const.min measurable_id).aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rcases le_total Q d with h | h
  · rw [min_eq_left h]; linarith [abs_nonneg d]
  · rw [min_eq_right h]; linarith [abs_nonneg Q]

lemma sc_rv (P : ContractData) : 0 < P.r - P.v := by
  have := P.profitable; have := P.cs_nonneg; have := P.v_lt_cr; linarith

lemma sc_K (P : ContractData) : 0 < P.r - P.v + P.p := by
  have := sc_rv P; have := P.ps_nonneg; have := P.pr_nonneg
  simp only [ContractData.p]; linarith

lemma sc_cv (P : ContractData) : 0 < P.c - P.v := by
  have := P.cs_nonneg; have := P.v_lt_cr; simp only [ContractData.c]; linarith

lemma sc_kappa (P : ContractData) :
    0 < (P.c - P.v) / (P.r - P.v + P.p) ∧ (P.c - P.v) / (P.r - P.v + P.p) < 1 := by
  have hK := sc_K P
  refine ⟨div_pos (sc_cv P) hK, (div_lt_one hK).mpr ?_⟩
  have := P.profitable; have := P.ps_nonneg; have := P.pr_nonneg
  simp only [ContractData.c, ContractData.p]; linarith

lemma sc_cdf_cont (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D] :
    Continuous (cdf D) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hmono := monotone_cdf D
  have hleft : Function.leftLim (cdf D) a = cdf D a := by
    have h1 := (cdf D).measure_singleton a
    rw [measure_cdf, measure_singleton] at h1
    have h2 := ENNReal.ofReal_eq_zero.mp h1.symm
    have h3 := hmono.leftLim_le (le_refl a)
    linarith
  have hl : ContinuousWithinAt (cdf D) (Set.Iio a) a :=
    hmono.continuousWithinAt_Iio_iff_leftLim_eq.mpr hleft
  have hr : ContinuousWithinAt (cdf D) (Set.Ioi a) a :=
    ((cdf D).right_continuous a).mono Set.Ioi_subset_Ici_self
  exact continuousAt_iff_continuous_left'_right'.mpr ⟨hl, hr⟩

lemma sc_exists_fractile (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (κ : ℝ) (h0 : 0 < κ) (h1 : κ < 1) : ∃ Q, 1 - cdf D Q = κ := by
  have hc := sc_cdf_cont D
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot D).eventually
    (gt_mem_nhds (by linarith : (0:ℝ) < 1 - κ))).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop D).eventually
    (lt_mem_nhds (by linarith : 1 - κ < 1))).exists
  obtain ⟨Q, hQ⟩ := intermediate_value_univ a b hc ⟨ha.le, hb.le⟩
  exact ⟨Q, by linarith⟩

lemma sc_sales_deriv (D : Measure ℝ) [IsProbabilityMeasure D] [NullSingletonClass D]
    (hD : Integrable (fun x => x) D) (Q0 : ℝ) :
    HasDerivAt (expSales D) (1 - cdf D Q0) Q0 := by
  have hlip : ∀ d : ℝ, LipschitzOnWith (Real.nnabs 1) (fun Q : ℝ => min Q d) Set.univ := by
    intro d
    have : Real.nnabs 1 = 1 := by simp
    rw [this]
    exact (LipschitzWith.id.min_const d).lipschitzOnWith
  have hdiff : ∀ d : ℝ, d ≠ Q0 →
      HasDerivAt (fun Q : ℝ => min Q d) (if Q0 < d then (1:ℝ) else 0) Q0 := by
    intro d hd
    rcases lt_or_gt_of_ne hd with h | h
    · rw [if_neg (not_lt.mpr h.le)]
      apply (hasDerivAt_const Q0 d).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds h] with Q hQ
      exact min_eq_right (le_of_lt hQ)
    · rw [if_pos h]
      apply (hasDerivAt_id Q0).congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds h] with Q hQ
      exact min_eq_left (le_of_lt hQ)
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := D)
    (F := fun Q d => min Q d) (F' := fun d => if Q0 < d then (1:ℝ) else 0)
    (bound := fun _ => (1:ℝ)) (s := Set.univ) (x₀ := Q0) Filter.univ_mem
    (Filter.Eventually.of_forall fun Q =>
      (measurable_const.min measurable_id).aestronglyMeasurable)
    (sc_int_min D hD Q0)
    ((Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun d => hlip d)
    (integrable_const 1)
    ((Measure.ae_ne D Q0).mono fun d hd => hdiff d hd)
  have hval : ∫ d, (if Q0 < d then (1:ℝ) else 0) ∂D = 1 - cdf D Q0 := by
    have e : (fun d : ℝ => if Q0 < d then (1:ℝ) else 0) = (Set.Ioi Q0).indicator 1 := by
      funext d; simp [Set.indicator_apply]
    rw [e, integral_indicator_one measurableSet_Ioi, cdf_eq_real, ← Set.compl_Iic,
      measureReal_compl measurableSet_Iic, probReal_univ]
  rw [← hval]
  exact key.2

section Unimodal

variable (D : Measure ℝ) [IsProbabilityMeasure D] (f : ℝ → ℝ)

lemma wu_cdf_eq (hdens : D = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : ContinuousOn f (Set.Ici 0)) (hfpos : ∀ x, 0 < x → 0 < f x) (x : ℝ) (hx : 0 ≤ x) :
    cdf D x = cdf D 0 + ∫ t in (0:ℝ)..x, f t := by
  have hint : IntegrableOn f (Set.Ioc 0 x) volume :=
    ((hf.mono Set.Icc_subset_Ici_self).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 x)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hfpos t ht.1).le
  have hD : D (Set.Ioc 0 x) = ENNReal.ofReal (∫ t in Set.Ioc 0 x, f t) := by
    rw [hdens, withDensity_apply _ measurableSet_Ioc, ofReal_integral_eq_lintegral_ofReal hint hnn]
  rw [cdf_eq_real, cdf_eq_real, intervalIntegral.integral_of_le hx,
    ← Set.Iic_union_Ioc_eq_Iic hx,
    measureReal_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc, measureReal_def (s := Set.Ioc 0 x), hD,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioc fun t ht => (hfpos t ht.1).le)]

lemma wu_cdf_deriv (hdens : D = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : ContinuousOn f (Set.Ici 0)) (hfpos : ∀ x, 0 < x → 0 < f x) (Q : ℝ) (hQ : 0 < Q) :
    HasDerivAt (fun x => cdf D x) (f Q) Q := by
  have hcQ : ContinuousAt f Q := hf.continuousAt (Ici_mem_nhds hQ)
  have hII : IntervalIntegrable f volume 0 Q := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hQ.le]
    exact hf.mono Set.Icc_subset_Ici_self
  have hsm : StronglyMeasurableAtFilter f (nhds Q) volume :=
    (hf.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi Q hQ
  have h1 : HasDerivAt (fun x => ∫ t in (0:ℝ)..x, f t) (f Q) Q :=
    intervalIntegral.integral_hasDerivAt_right hII hsm hcQ
  have h2 : HasDerivAt (fun x => cdf D 0 + ∫ t in (0:ℝ)..x, f t) (f Q) Q := h1.const_add _
  apply h2.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hQ] with x hx
  exact wu_cdf_eq D f hdens hf hfpos x (le_of_lt hx)

lemma wu_cdf_strict (hdens : D = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : ContinuousOn f (Set.Ici 0)) (hfpos : ∀ x, 0 < x → 0 < f x) (x y : ℝ) (hx : 0 ≤ x)
    (hxy : x < y) : cdf D x < cdf D y := by
  have hy : 0 ≤ y := hx.trans hxy.le
  have hII : ∀ z, 0 ≤ z → IntervalIntegrable f volume 0 z := fun z hz => by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hz]
    exact hf.mono Set.Icc_subset_Ici_self
  have hdiff : cdf D y - cdf D x = ∫ t in x..y, f t := by
    rw [wu_cdf_eq D f hdens hf hfpos y hy, wu_cdf_eq D f hdens hf hfpos x hx]
    rw [show cdf D 0 + (∫ t in (0:ℝ)..y, f t) - (cdf D 0 + ∫ t in (0:ℝ)..x, f t)
      = (∫ t in (0:ℝ)..y, f t) - ∫ t in (0:ℝ)..x, f t by ring]
    exact intervalIntegral.integral_interval_sub_left (hII y hy) (hII x hx)
  have hpos : 0 < ∫ t in x..y, f t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on _ _ hxy
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hxy.le]
      exact hf.mono fun t ht => hx.trans ht.1
    · intro t ht
      exact hfpos t (lt_of_le_of_lt hx ht.1)
  linarith

lemma wu_surv_pos (hdens : D = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : ContinuousOn f (Set.Ici 0)) (hfpos : ∀ x, 0 < x → 0 < f x) (x : ℝ) (hx : 0 ≤ x) :
    0 < 1 - cdf D x := by
  have := wu_cdf_strict D f hdens hf hfpos x (x + 1) hx (by linarith)
  have := cdf_le_one D (x + 1)
  linarith

end Unimodal

theorem wu_main (P : ContractData) (D : Measure ℝ) [IsProbabilityMeasure D]
    (hD : Integrable (fun x => x) D) (f : ℝ → ℝ)
    (hdens : D = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : ContinuousOn f (Set.Ici 0)) (hfpos : ∀ x, 0 < x → 0 < f x) (hIGFR : IGFR f D)
    (hQ0 : (P.c - P.v) / (P.r - P.v + P.p) < 1 - cdf D 0) :
    ∃ Qs, 0 < Qs ∧ StrictMonoOn (supplierInducedProfit P D) (Set.Icc 0 Qs)
      ∧ StrictAntiOn (supplierInducedProfit P D) (Set.Ici Qs) := by
  haveI : NullSingletonClass D := ⟨fun x => by
    rw [hdens]; exact withDensity_absolutelyContinuous _ _ Real.volume_singleton⟩
  set K := P.r - P.v + P.p with hK
  set a := P.r - P.v + P.pr with ha
  have hKpos : 0 < K := sc_K P
  have hcv : 0 < P.c - P.v := sc_cv P
  have hapos : 0 < a := by have := sc_rv P; have := P.pr_nonneg; linarith
  -- the derivative, as an explicit expression
  set h : ℝ → ℝ := fun Q => K * (1 - cdf D Q) - a * Q * f Q - (P.c - P.v) with hh
  have hπ : supplierInducedProfit P D = fun Q => P.ps * expSales D Q - P.cs * Q
      - P.ps * meanDemand D + (a * (1 - cdf D Q) - (P.cr - P.v)) * Q := rfl
  have hderiv : ∀ Q, 0 < Q → HasDerivAt (supplierInducedProfit P D) (h Q) Q := by
    intro Q hQ
    have hS := sc_sales_deriv D hD Q
    have hF := wu_cdf_deriv D f hdens hf hfpos Q hQ
    have hd : HasDerivAt (fun Q => P.ps * expSales D Q - P.cs * Q
        - P.ps * meanDemand D + (a * (1 - cdf D Q) - (P.cr - P.v)) * Q) _ Q :=
      (((hS.const_mul P.ps).sub ((hasDerivAt_id' Q).const_mul P.cs)).sub_const
        (P.ps * meanDemand D)).add
        ((((hF.const_sub 1).const_mul a).sub_const (P.cr - P.v)).mul (hasDerivAt_id' Q))
    rw [hπ]
    refine hd.congr_deriv ?_
    simp only [hh, hK, ha, ContractData.c, ContractData.p]
    ring
  have hπcont : Continuous (supplierInducedProfit P D) := by
    have hSc : Continuous (expSales D) :=
      continuous_iff_continuousAt.mpr fun x => (sc_sales_deriv D hD x).continuousAt
    have hFc := sc_cdf_cont D
    rw [hπ]
    fun_prop
  -- the survival function and the generalized failure rate
  have hG : ∀ Q, 0 ≤ Q → 0 < 1 - cdf D Q := wu_surv_pos D f hdens hf hfpos
  set ψ : ℝ → ℝ := fun Q => K - a * (Q * f Q / (1 - cdf D Q)) - (P.c - P.v) / (1 - cdf D Q)
    with hψ
  have hhψ : ∀ Q, 0 ≤ Q → h Q = (1 - cdf D Q) * ψ Q := by
    intro Q hQ
    have := (hG Q hQ).ne'
    simp only [hh, hψ]
    field_simp
  have hψanti : ∀ x y, 0 < x → x < y → ψ y < ψ x := by
    intro x y hx hxy
    have hy : 0 < y := hx.trans hxy
    have hg : x * f x / (1 - cdf D x) ≤ y * f y / (1 - cdf D y) :=
      hIGFR (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) hxy.le
    have hGy := hG y hy.le
    have hGxy : 1 - cdf D y < 1 - cdf D x := by
      have := wu_cdf_strict D f hdens hf hfpos x y hx.le hxy
      linarith
    have h1 : (P.c - P.v) / (1 - cdf D x) < (P.c - P.v) / (1 - cdf D y) :=
      div_lt_div_of_pos_left hcv hGy hGxy
    have h2 : a * (x * f x / (1 - cdf D x)) ≤ a * (y * f y / (1 - cdf D y)) :=
      mul_le_mul_of_nonneg_left hg hapos.le
    simp only [hψ]
    linarith
  -- a zero of the derivative
  have hcontOn : ∀ M, ContinuousOn h (Set.Icc 0 M) := by
    intro M
    have hfM : ContinuousOn f (Set.Icc 0 M) := hf.mono Set.Icc_subset_Ici_self
    have hFc := sc_cdf_cont D
    simp only [hh]
    fun_prop
  have h0 : 0 < h 0 := by
    have : P.c - P.v < K * (1 - cdf D 0) := by
      rw [div_lt_iff₀ hKpos] at hQ0
      linarith
    simp only [hh]
    linarith
  obtain ⟨M, hM1, hMF⟩ : ∃ M : ℝ, 1 ≤ M ∧ 1 - (P.c - P.v) / K < cdf D M := by
    have ht := (tendsto_cdf_atTop D).eventually
      (lt_mem_nhds (by have := div_pos hcv hKpos; linarith : 1 - (P.c - P.v) / K < 1))
    obtain ⟨M, hM⟩ := (ht.and (Filter.eventually_ge_atTop 1)).exists
    exact ⟨M, hM.2, hM.1⟩
  have hMneg : h M < 0 := by
    have hfM : 0 < f M := hfpos M (by linarith)
    have h1 : 0 ≤ a * M * f M := by positivity
    have h2 : K * (1 - cdf D M) < P.c - P.v := by
      have : 1 - cdf D M < (P.c - P.v) / K := by linarith
      rwa [lt_div_iff₀ hKpos, mul_comm] at this
    simp only [hh]
    linarith
  obtain ⟨Qs, hQsI, hQs0⟩ : ∃ Qs ∈ Set.Icc 0 M, h Qs = 0 :=
    intermediate_value_Icc' (by linarith) (hcontOn M) ⟨hMneg.le, h0.le⟩
  have hQspos : 0 < Qs := by
    rcases hQsI.1.eq_or_lt with heq | hlt
    · rw [← heq] at hQs0; linarith
    · exact hlt
  have hψQs : ψ Qs = 0 := by
    have := hhψ Qs hQspos.le
    rw [hQs0] at this
    rcases mul_eq_zero.mp this.symm with h' | h'
    · exact absurd h' (hG Qs hQspos.le).ne'
    · exact h'
  refine ⟨Qs, hQspos, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Icc 0 Qs) hπcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x hx.1).deriv, hhψ x hx.1.le]
    have := hψanti x Qs hx.1 hx.2
    exact mul_pos (hG x hx.1.le) (by linarith)
  · apply strictAntiOn_of_deriv_neg (convex_Ici Qs) hπcont.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := hQspos.trans hx
    rw [(hderiv x hx0).deriv, hhψ x hx0.le]
    have := hψanti Qs x hQspos hx
    exact mul_neg_of_pos_of_neg (hG x hx0.le) (by linarith)

end SupplyChainTheory

open SupplyChainTheory

theorem solution (P : ContractData) (D : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure D]
    (hD : MeasureTheory.Integrable (fun x => x) D) (f : ℝ → ℝ)
    (hdens : D = MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hf : ContinuousOn f (Set.Ici 0)) (hfpos : ∀ x, 0 < x → 0 < f x) (hIGFR : IGFR f D)
    (hQ0 : (P.c - P.v) / (P.r - P.v + P.p) < 1 - ProbabilityTheory.cdf D 0) :
    ∃ Qs, 0 < Qs ∧ StrictMonoOn (supplierInducedProfit P D) (Set.Icc 0 Qs)
      ∧ StrictAntiOn (supplierInducedProfit P D) (Set.Ici Qs) := by
  exact wu_main P D hD f hdens hf hfpos hIGFR hQ0
