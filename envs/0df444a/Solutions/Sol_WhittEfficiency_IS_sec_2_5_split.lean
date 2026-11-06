-- Prove2me | solution 1 for WhittEfficiency.IS.sec_2_5_split
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T05:51:10.090315+00:00
-- url     : https://prove2.me/submissions/6a97dfe3-9498-4639-a98a-dcf226360cf9

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model


open MeasureTheory ProbabilityTheory Filter Topology QueueingFundamentals.Foundations

namespace WhittSplit

lemma pdf_eq (r y : ℝ) : exponentialPDFReal r y = if 0 ≤ y then r * Real.exp (-(r * y)) else 0 := by
  simp [exponentialPDFReal, gammaPDFReal]

lemma pdf_nonneg' {r : ℝ} (hr : 0 < r) (y : ℝ) : 0 ≤ exponentialPDFReal r y :=
  exponentialPDFReal_nonneg hr y

lemma pdf_integrable {r : ℝ} (hr : 0 < r) : Integrable (exponentialPDFReal r) := by
  refine ⟨(measurable_exponentialPDFReal r).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (pdf_nonneg' hr))]
  have := lintegral_exponentialPDF_eq_one hr
  simp only [exponentialPDF] at this
  rw [this]; simp

lemma pdf_integral {r : ℝ} (hr : 0 < r) : ∫ y, exponentialPDFReal r y = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (pdf_nonneg' hr))
    (measurable_exponentialPDFReal r).aestronglyMeasurable]
  have := lintegral_exponentialPDF_eq_one hr
  simp only [exponentialPDF] at this
  rw [this]; simp

lemma pdf_Ioi {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) :
    ∫ y in Set.Ioi t, exponentialPDFReal r y = Real.exp (-(r * t)) := by
  have h1 := integral_add_compl (s := Set.Iic t) measurableSet_Iic (pdf_integrable hr)
  rw [Set.compl_Iic, pdf_integral hr, ← cdf_expMeasure_eq_integral hr, cdf_expMeasure_eq hr,
    if_pos ht] at h1
  linarith

/-- survival function of `gap 0 + ... + gap (m-1)` -/
noncomputable def surv (r : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  if s < 0 then 1 else Real.exp (-(r * s)) * ∑ k ∈ Finset.range m, (r * s) ^ k / (Nat.factorial k : ℝ)

lemma surv_meas (r : ℝ) (m : ℕ) : Measurable (surv r m) := by
  unfold surv
  refine Measurable.ite measurableSet_Iio measurable_const ?_
  fun_prop

lemma surv_nonneg {r : ℝ} (hr : 0 < r) (m : ℕ) (s : ℝ) : 0 ≤ surv r m s := by
  unfold surv
  split_ifs with h
  · norm_num
  · push_neg at h
    refine mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun k _ => ?_)
    positivity

lemma surv_le_one {r : ℝ} (hr : 0 < r) (m : ℕ) (s : ℝ) : surv r m s ≤ 1 := by
  unfold surv
  split_ifs with h
  · exact le_rfl
  · push_neg at h
    have hx : 0 ≤ r * s := mul_nonneg hr.le h
    have hs : ∑ k ∈ Finset.range m, (r * s) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (r * s) := by
      have := (NormedSpace.expSeries_div_hasSum_exp (r * s))
      rw [← Real.exp_eq_exp_ℝ] at this
      exact this.nonneg (fun k => by positivity) |> fun _ =>
        sum_le_hasSum (Finset.range m) (fun k _ => by positivity) this
    calc Real.exp (-(r * s)) * ∑ k ∈ Finset.range m, (r * s) ^ k / (Nat.factorial k : ℝ)
        ≤ Real.exp (-(r * s)) * Real.exp (r * s) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp

lemma surv_integral {r : ℝ} (hr : 0 < r) (m : ℕ) (t : ℝ) :
    ∫ y, surv r m (t - y) * exponentialPDFReal r y = surv r (m + 1) t := by
  rcases lt_or_ge t 0 with ht | ht
  · have : ∀ y, surv r m (t - y) * exponentialPDFReal r y = exponentialPDFReal r y := by
      intro y
      rcases lt_or_ge y 0 with hy | hy
      · rw [pdf_eq, if_neg (not_le.2 hy)]; simp
      · rw [surv, if_pos (by linarith)]; simp
    simp_rw [this, pdf_integral hr, surv, if_pos ht]
  have hint : Integrable (fun y => surv r m (t - y) * exponentialPDFReal r y) := by
    refine Integrable.mono' (pdf_integrable hr) ?_ (Eventually.of_forall fun y => ?_)
    · exact (((surv_meas r m).comp (measurable_const.sub measurable_id)).mul
        (measurable_exponentialPDFReal r)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (surv_nonneg hr _ _) (pdf_nonneg' hr _))]
      exact mul_le_of_le_one_left (pdf_nonneg' hr _) (surv_le_one hr _ _)
  rw [← integral_add_compl (s := Set.Iic t) measurableSet_Iic hint, Set.compl_Iic]
  have hIoi : ∫ y in Set.Ioi t, surv r m (t - y) * exponentialPDFReal r y = Real.exp (-(r * t)) := by
    rw [← pdf_Ioi hr ht]
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    simp only [Set.mem_Ioi] at hy
    rw [surv, if_pos (by linarith)]; simp
  have hIic : ∫ y in Set.Iic t, surv r m (t - y) * exponentialPDFReal r y =
      ∫ y in (0:ℝ)..t, r * Real.exp (-(r * t)) *
        ∑ k ∈ Finset.range m, (r * (t - y)) ^ k / (Nat.factorial k : ℝ) := by
    have hu : Set.Iic t = Set.Iio 0 ∪ Set.Icc 0 t := by
      ext y; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_Icc]
      constructor
      · intro h; by_cases h0 : y < 0
        · exact Or.inl h0
        · exact Or.inr ⟨not_lt.1 h0, h⟩
      · rintro (h | h) <;> [linarith; exact h.2]
    rw [hu, setIntegral_union (by
        rw [Set.disjoint_left]; intro y h1 h2; simp only [Set.mem_Iio, Set.mem_Icc] at h1 h2
        linarith) measurableSet_Icc hint.integrableOn hint.integrableOn]
    rw [setIntegral_eq_zero_of_forall_eq_zero (fun y hy => by
      simp only [Set.mem_Iio] at hy; rw [pdf_eq, if_neg (not_le.2 hy)]; simp), zero_add,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    rw [Set.uIcc_of_le ht] at hy
    obtain ⟨hy0, hyt⟩ := hy
    rw [pdf_eq, if_pos hy0, surv, if_neg (by linarith)]
    have : Real.exp (-(r * (t - y))) * Real.exp (-(r * y)) = Real.exp (-(r * t)) := by
      rw [← Real.exp_add]; congr 1; ring
    linear_combination (∑ k ∈ Finset.range m, (r * (t - y)) ^ k / (Nat.factorial k : ℝ)) * r * this
  rw [hIoi, hIic, intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (fun k _ => by apply Continuous.intervalIntegrable; fun_prop)]
  have hk : ∀ k : ℕ, ∫ y in (0:ℝ)..t, (r * (t - y)) ^ k / (Nat.factorial k : ℝ) =
      r ^ k / (Nat.factorial k : ℝ) * (t ^ (k + 1) / (k + 1)) := by
    intro k
    simp_rw [mul_pow, div_eq_mul_inv]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x => x ^ k), integral_pow]
    simp; ring
  simp_rw [hk]
  rw [surv, if_neg (not_lt.2 ht), Finset.sum_range_succ', mul_add, Finset.mul_sum]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Nat.factorial_succ]; push_cast
    field_simp
    ring
  · simp


lemma step_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P) {r : ℝ}
    (hr : 0 < r) (hYl : P.map Y = expMeasure r) (h : ℝ → ℝ) (hh : Measurable h)
    (h0 : ∀ s, 0 ≤ h s) (h1 : ∀ s, h s ≤ 1)
    (hXl : ∀ s, P {ω | s < X ω} = ENNReal.ofReal (h s)) (t : ℝ) :
    P {ω | t < X ω + Y ω} = ENNReal.ofReal (∫ y, h (t - y) * exponentialPDFReal r y) := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | t < p.1 + p.2} :=
    measurableSet_lt measurable_const (measurable_fst.add measurable_snd)
  have e1 : P {ω | t < X ω + Y ω} = P.map (fun ω => (X ω, Y ω)) {p | t < p.1 + p.2} := by
    rw [Measure.map_apply (hX.prodMk hY) hmeas]; rfl
  rw [e1, (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hind,
    Measure.prod_apply_symm hmeas, hYl]
  have e2 : ∀ y, P.map X ((fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | t < p.1 + p.2}) =
      ENNReal.ofReal (h (t - y)) := by
    intro y
    have hpre : (fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | t < p.1 + p.2} = {x : ℝ | t - y < x} := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor <;> intro <;> linarith
    rw [hpre, show {x : ℝ | t - y < x} = Set.Ioi (t - y) from rfl,
      Measure.map_apply hX measurableSet_Ioi, ← hXl]
    rfl
  simp_rw [e2]
  have hint : Integrable (fun y => h (t - y) * exponentialPDFReal r y) := by
    refine Integrable.mono' (pdf_integrable hr) ?_ (Eventually.of_forall fun y => ?_)
    · exact ((hh.comp (measurable_const.sub measurable_id)).mul
        (measurable_exponentialPDFReal r)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 _) (pdf_nonneg' hr _))]
      exact mul_le_of_le_one_left (pdf_nonneg' hr _) (h1 _)
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun y => mul_nonneg (h0 _) (pdf_nonneg' hr _))]
  show ∫⁻ y, ENNReal.ofReal (h (t - y)) ∂(volume.withDensity
    (fun x => ENNReal.ofReal (exponentialPDFReal r x))) = _
  have hgm : Measurable (fun y => ENNReal.ofReal (h (t - y))) :=
    (hh.comp (measurable_const.sub measurable_id)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_exponentialPDFReal r).ennreal_ofReal hgm]
  refine lintegral_congr (fun y => ?_)
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (pdf_nonneg' hr _), mul_comm]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {lam : ℝ} {T : ℕ → Ω → ℝ}

/-- number of arrivals `A_{k+1} ≤ t` -/
noncomputable def Ncount (T : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | arrivalTime T (k + 1) ω ≤ t}.ncard

lemma psum_meas (hT : IsExpInterarrivals μ lam T) (m : ℕ) : Measurable (arrivalTime T m) := by
  unfold arrivalTime
  exact Finset.measurable_sum _ (fun i _ => hT.measurable i)

lemma psum_indep [IsProbabilityMeasure μ] (hT : IsExpInterarrivals μ lam T) (m : ℕ) :
    IndepFun (arrivalTime T m) (T m) μ := by
  have h := hT.indep.indepFun_finsetSum_of_notMem (fun i => hT.measurable i)
    (s := Finset.range m) (i := m) (by simp)
  have e : (∑ j ∈ Finset.range m, T j) = arrivalTime T m := by
    funext ω; simp [arrivalTime, Finset.sum_apply]
  rw [e] at h
  exact h

lemma psum_surv [IsProbabilityMeasure μ] (hlam : 0 < lam) (hT : IsExpInterarrivals μ lam T)
    (m : ℕ) (s : ℝ) :
    μ {ω | s < arrivalTime T m ω} = ENNReal.ofReal (surv lam m s) := by
  induction m generalizing s with
  | zero =>
    simp only [arrivalTime, Finset.range_zero, Finset.sum_empty, surv, Finset.sum_empty, mul_zero]
    split_ifs with h
    · simp [h]
    · simp [h]
  | succ m ih =>
    have e : {ω | s < arrivalTime T (m + 1) ω} = {ω | s < arrivalTime T m ω + T m ω} := by
      ext ω; simp [arrivalTime, Finset.sum_range_succ]
    rw [e, step_law (psum_meas hT m) (hT.measurable m) (psum_indep hT m) hlam
      (hT.law m) (surv lam m) (surv_meas _ _) (surv_nonneg hlam m)
      (surv_le_one hlam m) ih s, surv_integral hlam]

lemma psum_mono {ω : Ω} (hω : ∀ k, 0 ≤ T k ω) {i j : ℕ}
    (hij : i ≤ j) : arrivalTime T i ω ≤ arrivalTime T j ω := by
  unfold arrivalTime
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hij)
    (fun k _ _ => hω k)

lemma count_iff {t : ℝ} (ht : 0 ≤ t) {ω : Ω}
    (hω : ∀ k, 0 ≤ T k ω) (hK : ∃ K, t < arrivalTime T K ω) (n : ℕ) :
    Ncount T t ω = n ↔ arrivalTime T n ω ≤ t ∧ t < arrivalTime T (n + 1) ω := by
  obtain ⟨K, hK⟩ := hK
  have hfin : {k : ℕ | arrivalTime T (k + 1) ω ≤ t}.Finite := by
    refine (Finset.finite_toSet (Finset.range K)).subset (fun k hk => ?_)
    simp only [Set.mem_setOf_eq] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h; push_neg at h
    have := psum_mono hω (show K ≤ k + 1 by omega)
    linarith
  unfold Ncount
  constructor
  · intro hc
    by_contra hneg
    rw [not_and_or, not_le, not_lt] at hneg
    rcases hneg with h | h
    · have hn : 1 ≤ n := by
        by_contra h0; push_neg at h0
        have : n = 0 := by omega
        subst this; simp [arrivalTime] at h; linarith
      have hsub : {k : ℕ | arrivalTime T (k + 1) ω ≤ t} ⊆ ↑(Finset.range (n - 1)) := by
        intro k hk
        simp only [Set.mem_setOf_eq] at hk
        simp only [Finset.coe_range, Set.mem_Iio]
        by_contra h'; push_neg at h'
        have := psum_mono hω (show n ≤ k + 1 by omega)
        linarith
      have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset, Finset.card_range, hc] at this
      omega
    · have hsub : (↑(Finset.range (n + 1)) : Set ℕ) ⊆ {k : ℕ | arrivalTime T (k + 1) ω ≤ t} := by
        intro k hk
        simp only [Finset.coe_range, Set.mem_Iio] at hk
        simp only [Set.mem_setOf_eq]
        have := psum_mono hω (show k + 1 ≤ n + 1 by omega)
        linarith
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset, Finset.card_range, hc] at this
      omega
  · rintro ⟨h1, h2⟩
    have : {k : ℕ | arrivalTime T (k + 1) ω ≤ t} = ↑(Finset.range n) := by
      ext k
      simp only [Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
      constructor
      · intro hk; by_contra h'; push_neg at h'
        have := psum_mono hω (show n + 1 ≤ k + 1 by omega)
        linarith
      · intro hk
        have := psum_mono hω (show k + 1 ≤ n by omega)
        linarith
    rw [this, Set.ncard_coe_finset, Finset.card_range]

lemma gap_nonneg_ae [IsProbabilityMeasure μ] (hlam : 0 < lam) (hT : IsExpInterarrivals μ lam T) :
    ∀ᵐ ω ∂μ, ∀ k, 0 ≤ T k ω := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have : {ω | ¬ 0 ≤ T k ω} = T k ⁻¹' Set.Iio 0 := by ext; simp
  rw [this, ← Measure.map_apply (hT.measurable k) measurableSet_Iio, hT.law k]
  haveI := isProbabilityMeasure_expMeasure hlam
  refine le_antisymm ?_ bot_le
  calc expMeasure lam (Set.Iio 0) ≤ expMeasure lam (Set.Iic 0) :=
        measure_mono Set.Iio_subset_Iic_self
    _ = ENNReal.ofReal (cdf (expMeasure lam) 0) := (ofReal_cdf _ _).symm
    _ = 0 := by rw [cdf_expMeasure_eq hlam, if_pos le_rfl]; simp

lemma surv_tendsto {r : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m => surv r m t) atTop (𝓝 1) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (r * t)).tendsto_sum_nat
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.const_mul (Real.exp (-(r * t)))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  refine h2.congr (fun m => ?_)
  rw [surv, if_neg (not_lt.2 ht)]

lemma finite_ae [IsProbabilityMeasure μ] (hlam : 0 < lam) (hT : IsExpInterarrivals μ lam T)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂μ, ∃ K, t < arrivalTime T K ω := by
  rw [ae_iff]
  have hb : ∀ m, (μ {ω | ¬ ∃ K, t < arrivalTime T K ω}).toReal ≤ 1 - surv lam m t := by
    intro m
    have hsub : {ω | ¬ ∃ K, t < arrivalTime T K ω} ⊆ {ω | t < arrivalTime T m ω}ᶜ := by
      intro ω hω h; exact hω ⟨m, h⟩
    have hms : MeasurableSet {ω | t < arrivalTime T m ω} :=
      measurableSet_lt measurable_const (psum_meas hT m)
    calc (μ {ω | ¬ ∃ K, t < arrivalTime T K ω}).toReal ≤ (μ {ω | t < arrivalTime T m ω}ᶜ).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ = 1 - surv lam m t := by
          rw [prob_compl_eq_one_sub hms, psum_surv hlam hT,
            ENNReal.toReal_sub_of_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (surv_le_one hlam m t)) ENNReal.one_ne_top,
            ENNReal.toReal_ofReal (surv_nonneg hlam m t)]
          simp
  have hlim : Tendsto (fun m => 1 - surv lam m t) atTop (𝓝 0) := by
    have := (surv_tendsto (r := lam) ht).const_sub 1
    simpa using this
  have h0 := ge_of_tendsto' hlim hb
  have h1 : (μ {ω | ¬ ∃ K, t < arrivalTime T K ω}).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
  rwa [ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h1

theorem order_count_core [IsProbabilityMeasure μ] (hlam : 0 < lam) (hT : IsExpInterarrivals μ lam T)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (μ {ω | Ncount T t ω = n}).toReal =
      Real.exp (-(lam * t)) * (lam * t) ^ n / (Nat.factorial n : ℝ) := by
  set A := {ω | t < arrivalTime T (n + 1) ω}
  set C := {ω | t < arrivalTime T n ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (psum_meas hT _)
  have hC : MeasurableSet C := measurableSet_lt measurable_const (psum_meas hT _)
  have e1 : μ {ω | Ncount T t ω = n} = μ (A \ C) := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [gap_nonneg_ae hlam hT, finite_ae hlam hT ht.le] with ω hω hK
    show Ncount T t ω = n ↔ ω ∈ A \ C
    rw [count_iff ht.le hω hK n]
    simp only [A, C, Set.mem_diff, Set.mem_setOf_eq, not_lt]
    tauto
  have e2 : μ (A ∩ C) = μ C := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [gap_nonneg_ae hlam hT] with ω hω
    simp only [A, C, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨lt_of_lt_of_le h (psum_mono hω (Nat.le_succ n)), h⟩
  have e3 := measure_inter_add_diff (μ := μ) A hC
  rw [e2] at e3
  have e4 : μ (A \ C) = μ A - μ C := by
    rw [← e3, ENNReal.add_sub_cancel_left (measure_ne_top _ _)]
  have hle : μ C ≤ μ A := by rw [← e3]; exact le_add_right le_rfl
  rw [e1, e4, ENNReal.toReal_sub_of_le hle (measure_ne_top _ _), psum_surv hlam hT,
    psum_surv hlam hT,
    ENNReal.toReal_ofReal (surv_nonneg hlam _ _),
    ENNReal.toReal_ofReal (surv_nonneg hlam _ _), surv, surv, if_neg (not_lt.2 ht.le),
    if_neg (not_lt.2 ht.le), Finset.sum_range_succ]
  ring


lemma lintegral_pi_prod {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
      Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → ℝ => ∏ x, f x.succ (y x))
      (hf 0).aemeasurable
      (Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable,
      ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf i.succ)]

lemma pi_exp_eq (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Measure.pi (fun _ : Fin n => expMeasure r) =
      volume.withDensity (fun v => ∏ i, ENNReal.ofReal (exponentialPDFReal r (v i))) := by
  have := isProbabilityMeasure_expMeasure hr
  refine Measure.pi_eq (μ := fun _ : Fin n => expMeasure r) (fun s hs => ?_)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    lintegral_pi_prod _ _ (fun i => (measurable_exponentialPDFReal r).ennreal_ofReal)]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [expMeasure, gammaMeasure, withDensity_apply _ (hs i)]
  rfl

lemma hyperplane_null {N : ℕ} (φ : (Fin N → ℝ) →ₗ[ℝ] ℝ) (d : ℝ) (w : Fin N → ℝ) (hw : φ w ≠ d) :
    volume {v : Fin N → ℝ | φ v = d} = 0 := by
  let s : AffineSubspace ℝ (Fin N → ℝ) :=
    { carrier := {v | φ v = d}
      smul_vsub_vadd_mem' := by
        intro c p1 p2 p3 h1 h2 h3
        simp only [Set.mem_setOf_eq, vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub] at *
        rw [h1, h2, h3]; simp }
  have hs : s ≠ ⊤ := by
    intro h
    have : w ∈ s := h ▸ AffineSubspace.mem_top ℝ _ w
    exact hw this
  exact Measure.addHaar_affineSubspace volume s hs


/-- extension of a finite vector by zero -/
noncomputable def extv {N : ℕ} (v : Fin N → ℝ) (k : ℕ) : ℝ := if h : k < N then v ⟨k, h⟩ else 0

/-- the partial-sum linear map -/
noncomputable def Lmap (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun v i := ∑ k ∈ Finset.range (i.val + 1), extv v k
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold extv; split_ifs <;> simp
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold extv; split_ifs <;> simp

lemma Lmap_apply {N : ℕ} (v : Fin N → ℝ) (i : Fin N) :
    Lmap N v i = ∑ k ∈ Finset.range (i.val + 1), extv v k := rfl

lemma Lmap_zero {m : ℕ} (v : Fin (m + 1) → ℝ) : Lmap (m + 1) v 0 = v 0 := by
  simp [Lmap_apply, extv]

lemma Lmap_succ {m : ℕ} (v : Fin (m + 1) → ℝ) (i : Fin m) :
    Lmap (m + 1) v i.succ = Lmap (m + 1) v i.castSucc + v i.succ := by
  rw [Lmap_apply, Lmap_apply, Fin.val_succ, Finset.sum_range_succ, Fin.coe_castSucc]
  congr 1
  simp only [extv, dif_pos (show (i.val + 1) < m + 1 by omega)]
  rfl

lemma Lmap_last {m : ℕ} (v : Fin (m + 1) → ℝ) : Lmap (m + 1) v (Fin.last m) = ∑ i, v i := by
  rw [Lmap_apply, Fin.val_last, ← Fin.sum_univ_eq_sum_range (fun k => extv v k)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [extv, dif_pos i.isLt]

lemma Lmap_det (N : ℕ) : LinearMap.det (Lmap N) = 1 := by
  rw [← LinearMap.det_toMatrix']
  have hent : ∀ i j : Fin N, LinearMap.toMatrix' (Lmap N) i j = if j ≤ i then 1 else 0 := by
    intro i j
    rw [LinearMap.toMatrix'_apply, Lmap_apply]
    split_ifs with hji
    · rw [Finset.sum_eq_single j.val]
      · simp [extv]
      · intro k _ hk
        simp only [extv]
        split_ifs with hkN
        · rw [Pi.single_apply, if_neg]; intro h; apply hk; rw [← h]
        · rfl
      · intro h; exfalso; apply h; simp only [Finset.mem_range]
        have : j.val ≤ i.val := hji
        omega
    · refine Finset.sum_eq_zero (fun k hk => ?_)
      simp only [Finset.mem_range] at hk
      simp only [extv]
      split_ifs with hkN
      · rw [Pi.single_apply, if_neg]; intro h
        have : j.val = k := by rw [← h]
        have : ¬ j.val ≤ i.val := hji
        omega
      · rfl
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one (fun i _ => ?_)
    rw [hent, if_pos le_rfl]
  · intro i j hij
    rw [hent, if_neg]
    simpa using hij


lemma exp_Ioi {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    expMeasure r (Set.Ioi x) = ENNReal.ofReal (Real.exp (-(r * x))) := by
  have := isProbabilityMeasure_expMeasure hr
  have hle : Real.exp (-(r * x)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, ← ofReal_cdf,
    cdf_expMeasure_eq hr, if_pos hx, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (by linarith)]
  congr 1; ring

lemma sumL_apply {N : ℕ} (v : Fin N → ℝ) :
    (∑ i, LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i) v = ∑ i, v i := by
  simp

theorem os_succ [IsProbabilityMeasure μ] (hlam : 0 < lam) (hT : IsExpInterarrivals μ lam T)
    {t : ℝ} (ht : 0 < t) (m : ℕ)
    {A : Set (Fin (m + 1) → ℝ)} (hA : MeasurableSet A) :
    μ ({ω | Ncount T t ω = m + 1} ∩ {ω | (fun i : Fin (m + 1) => arrivalTime T (i + 1) ω) ∈ A}) =
      ENNReal.ofReal (lam ^ (m + 1) * Real.exp (-(lam * t))) *
        volume (A ∩ {x : Fin (m + 1) → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t}) := by
  set O := {x : Fin (m + 1) → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t} with hO
  set r := lam with hr_def
  have hr : 0 < r := hlam
  let gv : Ω → (Fin (m + 1) → ℝ) := fun ω i => T i ω
  have hgv : Measurable gv := measurable_pi_lambda _ (fun i => hT.measurable i)
  have harr : ∀ ω, (fun i : Fin (m + 1) => arrivalTime T (i + 1) ω) = Lmap (m + 1) (gv ω) := by
    intro ω; funext i
    rw [Lmap_apply]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range] at hk
    simp only [extv, dif_pos (show k < m + 1 by omega), gv]
  have hps : ∀ ω, arrivalTime T (m + 1) ω = ∑ i, gv ω i := by
    intro ω
    simp only [arrivalTime, gv]
    exact (Fin.sum_univ_eq_sum_range (fun k => T k ω) (m + 1)).symm
  -- law of the gap vector
  have hI : iIndepFun (fun (i : Fin (m + 1)) ω => T i ω) μ :=
    hT.indep.precomp (g := fun i : Fin (m + 1) => i.val) Fin.val_injective
  have hlaw : μ.map gv = Measure.pi (fun _ : Fin (m + 1) => expMeasure r) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin (m + 1)) ω => T i ω)
      (fun i : Fin (m + 1) => (hT.measurable i).aemeasurable)).1 hI]
    congr 1; funext i; exact hT.law i
  have hind : IndepFun gv (T (m + 1)) μ := by
    have hd : Disjoint (Finset.range (m + 1)) ({m + 1} : Finset ℕ) := by
      rw [Finset.disjoint_singleton_right]; simp
    have h1 := hT.indep.indepFun_finset _ _ hd (fun i => hT.measurable i)
    have hmem : ∀ i : Fin (m + 1), i.val ∈ Finset.range (m + 1) := by
      intro i; simp only [Finset.mem_range]; exact i.isLt
    have hφ : Measurable (fun v : Finset.range (m + 1) → ℝ => fun i : Fin (m + 1) => v ⟨i.val, hmem i⟩) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have hψ : Measurable (fun v : ({m + 1} : Finset ℕ) → ℝ =>
        v ⟨m + 1, Finset.mem_singleton_self _⟩) := measurable_pi_apply _
    exact h1.comp hφ hψ
  -- the event
  let W : Set ((Fin (m + 1) → ℝ) × ℝ) :=
    {p | Lmap (m + 1) p.1 ∈ A ∧ ∑ i, p.1 i ≤ t ∧ t < ∑ i, p.1 i + p.2}
  have hLm : Measurable (Lmap (m + 1)) :=
    (LinearMap.continuous_of_finiteDimensional (Lmap (m + 1))).measurable
  have hsm : Measurable (fun v : Fin (m + 1) → ℝ => ∑ i, v i) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hW : MeasurableSet W := by
    refine ((hLm.comp measurable_fst) hA).inter ((measurableSet_le (hsm.comp measurable_fst)
      measurable_const).inter (measurableSet_lt measurable_const
        ((hsm.comp measurable_fst).add measurable_snd)))
  have e1 : μ ({ω | Ncount T t ω = m + 1} ∩
      {ω | (fun i : Fin (m + 1) => arrivalTime T (i + 1) ω) ∈ A}) =
      μ ((fun ω => (gv ω, T (m + 1) ω)) ⁻¹' W) := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [gap_nonneg_ae hlam hT, finite_ae hlam hT ht.le] with ω hω hK
    show (Ncount T t ω = m + 1 ∧ (fun i : Fin (m + 1) => arrivalTime T (i + 1) ω) ∈ A) ↔
      (Lmap (m + 1) (gv ω) ∈ A ∧ ∑ i, gv ω i ≤ t ∧ t < ∑ i, gv ω i + T (m + 1) ω)
    rw [count_iff ht.le hω hK, harr, ← hps]
    have : arrivalTime T (m + 1 + 1) ω = arrivalTime T (m + 1) ω + T (m + 1) ω := by
      simp [arrivalTime, Finset.sum_range_succ]
    rw [this]
    tauto
  rw [e1, ← Measure.map_apply (hgv.prodMk (hT.measurable _)) hW,
    (indepFun_iff_map_prod_eq_prod_map_map hgv.aemeasurable
      (hT.measurable _).aemeasurable).1 hind, Measure.prod_apply hW, hlaw, hT.law,
    pi_exp_eq _ hr]
  set B : Set (Fin (m + 1) → ℝ) := {v | Lmap (m + 1) v ∈ A ∧ ∑ i, v i ≤ t} with hB
  have hBm : MeasurableSet B := (hLm hA).inter (measurableSet_le hsm measurable_const)
  have hsec : ∀ v, expMeasure r (Prod.mk v ⁻¹' W) =
      B.indicator (fun v => ENNReal.ofReal (Real.exp (-(r * (t - ∑ i, v i))))) v := by
    intro v
    by_cases hv : v ∈ B
    · rw [Set.indicator_of_mem hv, ← exp_Ioi hr (by have := hv.2; linarith)]
      congr 1; ext y
      simp only [W, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioi]
      constructor
      · rintro ⟨_, _, h⟩; linarith
      · intro h; exact ⟨hv.1, hv.2, by linarith⟩
    · rw [Set.indicator_of_notMem hv]
      have : Prod.mk v ⁻¹' W = ∅ := by
        ext y; simp only [W, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨h1, h2, _⟩; exact hv ⟨h1, h2⟩
      rw [this, measure_empty]
  refine (lintegral_congr hsec).trans ?_
  have hDm : Measurable (fun v : Fin (m + 1) → ℝ =>
      ∏ i, ENNReal.ofReal (exponentialPDFReal r (v i))) :=
    Finset.measurable_prod _ (fun i _ =>
      ((measurable_exponentialPDFReal r).comp (measurable_pi_apply i)).ennreal_ofReal)
  have hFm : Measurable (B.indicator
      (fun v : Fin (m + 1) → ℝ => ENNReal.ofReal (Real.exp (-(r * (t - ∑ i, v i)))))) := by
    refine Measurable.indicator ?_ hBm
    exact (Real.measurable_exp.comp ((measurable_const.sub hsm).const_mul r).neg).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hDm hFm]
  set Pos : Set (Fin (m + 1) → ℝ) := {v | ∀ i, 0 ≤ v i} with hPos
  have hPm : MeasurableSet Pos := by
    have : Pos = ⋂ i, {v : Fin (m + 1) → ℝ | 0 ≤ v i} := by ext v; simp [Pos]
    rw [this]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  have hpt : ∀ v, ((fun v : Fin (m + 1) → ℝ => ∏ i, ENNReal.ofReal (exponentialPDFReal r (v i))) *
      B.indicator (fun v => ENNReal.ofReal (Real.exp (-(r * (t - ∑ i, v i)))))) v =
      (B ∩ Pos).indicator (fun _ => ENNReal.ofReal (r ^ (m + 1) * Real.exp (-(r * t)))) v := by
    intro v
    simp only [Pi.mul_apply]
    by_cases hv : v ∈ B
    · rw [Set.indicator_of_mem hv]
      by_cases hp : v ∈ Pos
      · rw [Set.indicator_of_mem (show v ∈ B ∩ Pos from ⟨hv, hp⟩)]
        have : ∀ i, exponentialPDFReal r (v i) = r * Real.exp (-(r * v i)) := by
          intro i; rw [pdf_eq, if_pos (hp i)]
        simp_rw [this]
        rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), ← ENNReal.ofReal_mul
          (Finset.prod_nonneg (fun i _ => by positivity))]
        congr 1
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.exp_sum, mul_assoc, ← Real.exp_add]
        congr 2
        simp only [Finset.sum_neg_distrib, ← Finset.mul_sum]
        ring
      · rw [Set.indicator_of_notMem (fun h => hp h.2)]
        simp only [Pos, Set.mem_setOf_eq, not_forall, not_le] at hp
        obtain ⟨i, hi⟩ := hp
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [pdf_eq, if_neg (not_le.2 hi)]; simp),
          zero_mul]
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv h.1), mul_zero]
  rw [lintegral_congr hpt, lintegral_indicator_const (hBm.inter hPm)]
  suffices hvol : volume (B ∩ Pos) = volume (A ∩ O) by rw [hvol]
  -- volume comparison
  set Z : Set (Fin (m + 1) → ℝ) := (⋃ i, {v | v i = 0}) ∪ {v | ∑ i, v i = t} with hZ
  have hZ0 : volume Z = 0 := by
    refine measure_union_null (measure_iUnion_null (fun i => ?_)) ?_
    · have := hyperplane_null (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) i) 0
        (fun _ => 1) (by simp)
      simpa using this
    · have := hyperplane_null (∑ i, LinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) i) t
        0 (by rw [sumL_apply]; simp; linarith)
      simp_rw [sumL_apply] at this
      exact this
  have hsub1 : Lmap (m + 1) ⁻¹' (A ∩ O) ⊆ B ∩ Pos := by
    rintro v ⟨hvA, hvS, hvO⟩
    refine ⟨⟨hvA, ?_⟩, ?_⟩
    · rw [← Lmap_last]; exact (hvO (Fin.last m)).2.le
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
      · subst h; rw [← Lmap_zero v]; exact (hvO 0).1.le
      · have h1 := Lmap_succ v j
        have h2 := hvS (Fin.castSucc_lt_succ (i := j))
        linarith
  have hsub2 : B ∩ Pos ⊆ Lmap (m + 1) ⁻¹' (A ∩ O) ∪ Z := by
    rintro v ⟨⟨hvA, hvt⟩, hvp⟩
    by_cases hz : v ∈ Z
    · exact Or.inr hz
    left
    simp only [Z, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists] at hz
    have hpos : ∀ i, 0 < v i := fun i => lt_of_le_of_ne (hvp i) (fun h => hz.1 i h.symm)
    have hlt : ∑ i, v i < t := lt_of_le_of_ne hvt hz.2
    have hmono : StrictMono (Lmap (m + 1) v) := by
      rw [Fin.strictMono_iff_lt_succ]
      intro j; rw [Lmap_succ]; linarith [hpos j.succ]
    refine ⟨hvA, hmono, fun i => ⟨?_, ?_⟩⟩
    · have := hmono.monotone (Fin.zero_le i)
      rw [Lmap_zero] at this; linarith [hpos 0]
    · have := hmono.monotone (Fin.le_last i)
      rw [Lmap_last] at this; linarith
  have hpre : volume (Lmap (m + 1) ⁻¹' (A ∩ O)) = volume (A ∩ O) := by
    rw [Measure.addHaar_preimage_linearMap volume (by rw [Lmap_det]; norm_num), Lmap_det]
    simp
  apply le_antisymm
  · calc volume (B ∩ Pos) ≤ volume (Lmap (m + 1) ⁻¹' (A ∩ O) ∪ Z) := measure_mono hsub2
      _ ≤ volume (Lmap (m + 1) ⁻¹' (A ∩ O)) + volume Z := measure_union_le _ _
      _ = volume (A ∩ O) := by rw [hZ0, add_zero, hpre]
  · rw [← hpre]; exact measure_mono hsub1


end WhittSplit


open MeasureTheory ProbabilityTheory Filter Topology QueueingFundamentals.Foundations

namespace WhittSplit

/-- `ω ↦ #{j | ω ∈ C j}` is measurable when every `C j` is. -/
theorem measurable_ncard_setOf {Ω : Type*} [MeasurableSpace Ω] (C : ℕ → Set Ω)
    (hC : ∀ j, MeasurableSet (C j)) :
    Measurable (fun ω => {j : ℕ | ω ∈ C j}.ncard) := by
  apply measurable_to_countable'
  intro k
  have hfin : MeasurableSet {ω | {j : ℕ | ω ∈ C j}.Finite} := by
    have : {ω | {j : ℕ | ω ∈ C j}.Finite} = ⋃ N : ℕ, ⋂ j : ℕ, ⋂ (_ : N ≤ j), (C j)ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_compl_iff]
      constructor
      · intro h
        obtain ⟨N, hN⟩ := h.bddAbove
        refine ⟨N + 1, fun j hj hjC => ?_⟩
        have := hN hjC
        omega
      · rintro ⟨N, hN⟩
        apply (Set.finite_lt_nat N).subset
        intro j hj
        by_contra hjN
        exact hN j (by simp at hjN; omega) hj
    rw [this]
    exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => (hC j).compl
  have hEq : ∀ F : Finset ℕ, MeasurableSet {ω | {j : ℕ | ω ∈ C j} = (F : Set ℕ)} := by
    intro F
    have : {ω | {j : ℕ | ω ∈ C j} = (F : Set ℕ)} =
        ⋂ j : ℕ, {ω | ω ∈ C j ↔ j ∈ F} := by
      ext ω
      simp [Set.ext_iff]
    rw [this]
    refine MeasurableSet.iInter fun j => ?_
    by_cases hj : j ∈ F
    · have e : {ω | ω ∈ C j ↔ j ∈ F} = C j := by ext; simp [hj]
      rw [e]; exact hC j
    · have e : {ω | ω ∈ C j ↔ j ∈ F} = (C j)ᶜ := by ext; simp [hj]
      rw [e]; exact (hC j).compl
  have hset : (fun ω => {j : ℕ | ω ∈ C j}.ncard) ⁻¹' {k} =
      (⋃ F : Finset ℕ, ⋃ (_ : F.card = k), {ω | {j : ℕ | ω ∈ C j} = (F : Set ℕ)}) ∪
        ({ω | {j : ℕ | ω ∈ C j}.Finite}ᶜ ∩ {_ω | k = 0}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iUnion,
      Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · intro h
      by_cases hf : {j : ℕ | ω ∈ C j}.Finite
      · left
        refine ⟨hf.toFinset, ?_, by simp⟩
        rw [← h, Set.ncard_eq_toFinset_card _ hf]
      · right
        exact ⟨hf, by rw [← h, Set.Infinite.ncard hf]⟩
    · rintro (⟨F, hF, hS⟩ | ⟨hf, hk⟩)
      · rw [hS, Set.ncard_coe_finset, hF]
      · rw [hk, Set.Infinite.ncard hf]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun _ => hEq F) ?_
  refine hfin.compl.inter ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]


/-- the open ordered simplex `0 < s_0 < ⋯ < s_{n-1} < t` -/
def Osimp (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) := {x | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t}

lemma measurableSet_Osimp (n : ℕ) (t : ℝ) : MeasurableSet (Osimp n t) := by
  have : Osimp n t = (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {x : Fin n → ℝ | x i < x j}) ∩
      ⋂ i : Fin n, ({x : Fin n → ℝ | 0 < x i} ∩ {x | x i < t}) := by
    ext x
    simp only [Osimp, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rfl
  rw [this]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j))
    (MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt (measurable_pi_apply i) measurable_const))

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {lam : ℝ} {T : ℕ → Ω → ℝ}

theorem os_all [IsProbabilityMeasure μ] (hlam : 0 < lam) (hT : IsExpInterarrivals μ lam T)
    {t : ℝ} (ht : 0 < t) (n : ℕ) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    μ ({ω | Ncount T t ω = n} ∩ {ω | (fun i : Fin n => arrivalTime T (i + 1) ω) ∈ A}) =
      ENNReal.ofReal (lam ^ n * Real.exp (-(lam * t))) * volume (A ∩ Osimp n t) := by
  cases n with
  | zero =>
    have h0 := order_count_core hlam hT ht 0
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one] at h0
    have hO : Osimp 0 t = Set.univ := by
      ext x; simp only [Osimp, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨fun a => Fin.elim0 a, fun i => Fin.elim0 i⟩
    by_cases h : (fun i : Fin 0 => (0 : ℝ)) ∈ A
    · have hA' : A = Set.univ := by
        ext x; simp only [Set.mem_univ, iff_true]
        rwa [Subsingleton.elim x (fun i : Fin 0 => (0 : ℝ))]
      subst hA'
      have hv : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [volume_pi, Measure.pi_of_empty]; simp
      simp only [Set.mem_univ, Set.setOf_true, Set.inter_univ, hO, hv, mul_one, one_mul, pow_zero]
      rw [← h0, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    · have hA' : A = ∅ := by
        ext x; simp only [Set.mem_empty_iff_false, iff_false]
        rwa [Subsingleton.elim x (fun i : Fin 0 => (0 : ℝ))]
      subst hA'
      simp
  | succ m => exact os_succ hlam hT ht m hA

end WhittSplit


open MeasureTheory ProbabilityTheory Filter Topology QueueingFundamentals.Foundations

namespace WhittSplit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {lam : ℝ} {T : ℕ → Ω → ℝ}

/-- the label law `∑ᵢ pᵢ δᵢ` -/
noncomputable def cat {m : ℕ} (p : Fin m → ℝ) : Measure (Fin m) :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i

instance cat_finite {m : ℕ} (p : Fin m → ℝ) : IsFiniteMeasure (cat p) :=
  ⟨by
    simp only [cat, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (measure_lt_top _ _))⟩

lemma cat_singleton {m : ℕ} (p : Fin m → ℝ) (j : Fin m) :
    cat p {j} = ENNReal.ofReal (p j) := by
  classical
  simp only [cat, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton j), smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Set.indicator_of_notMem (show b ∉ ({j} : Set (Fin m)) by simpa using hb)]
  · simp

lemma map_J [IsProbabilityMeasure μ] {m : ℕ} {p : Fin m → ℝ} {J : ℕ → Ω → Fin m}
    (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J) (k : ℕ) :
    μ.map (J k) = cat p := by
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply (hM.label_measurable k) (measurableSet_singleton j), cat_singleton,
    ← hM.label_law k j, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rfl

lemma map_Jvec [IsProbabilityMeasure μ] {m : ℕ} {p : Fin m → ℝ} {J : ℕ → Ω → Fin m}
    (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J) (n : ℕ) :
    μ.map (fun ω (i : Fin n) => J i ω) = Measure.pi (fun _ => cat p) := by
  have hI : iIndepFun (fun (i : Fin n) ω => J i ω) μ :=
    hM.label_indep.precomp (g := fun i : Fin n => i.val) Fin.val_injective
  rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin n) ω => J i ω)
      (fun i : Fin n => (hM.label_measurable i).aemeasurable)).1 hI]
  congr 1; funext i; exact map_J hM i

lemma Ncount_measurable' {Ω' : Type*} [MeasurableSpace Ω'] {T' : ℕ → Ω' → ℝ}
    (hT' : ∀ k, Measurable (T' k)) (t : ℝ) : Measurable (Ncount T' t) := by
  have hA : ∀ k, Measurable (arrivalTime T' k) := fun k => by
    unfold arrivalTime; exact Finset.measurable_sum _ (fun i _ => hT' i)
  exact measurable_ncard_setOf (fun k => {ω | arrivalTime T' (k + 1) ω ≤ t})
    (fun k => measurableSet_le (hA _) measurable_const)

lemma Svec_measurable' {Ω' : Type*} [MeasurableSpace Ω'] {T' : ℕ → Ω' → ℝ}
    (hT' : ∀ k, Measurable (T' k)) (n : ℕ) :
    Measurable (fun ω (i : Fin n) => arrivalTime T' (i + 1) ω) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  unfold arrivalTime; exact Finset.measurable_sum _ (fun j _ => hT' j)

theorem joint_indep [IsProbabilityMeasure μ] {m : ℕ} {p : Fin m → ℝ} {J : ℕ → Ω → Fin m}
    (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J) (t : ℝ) (n : ℕ)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) (L : Set (Fin n → Fin m)) :
    μ (({ω | Ncount T t ω = n} ∩ {ω | (fun i : Fin n => arrivalTime T (i + 1) ω) ∈ A}) ∩
        {ω | (fun i : Fin n => J i ω) ∈ L}) =
      μ ({ω | Ncount T t ω = n} ∩ {ω | (fun i : Fin n => arrivalTime T (i + 1) ω) ∈ A}) *
        μ {ω | (fun i : Fin n => J i ω) ∈ L} := by
  set Tc : ℕ → (ℕ → ℝ) → ℝ := fun k τ => τ k
  have hTc : ∀ k, Measurable (Tc k) := fun k => measurable_pi_apply k
  set E : Set (ℕ → ℝ) := {τ | Ncount Tc t τ = n} ∩
    {τ | (fun i : Fin n => arrivalTime Tc (i + 1) τ) ∈ A}
  have hE : MeasurableSet E :=
    (Ncount_measurable' hTc t (measurableSet_singleton n)).inter (Svec_measurable' hTc n hA)
  set F : Set (ℕ → Fin m) := {ℓ | (fun i : Fin n => ℓ i) ∈ L}
  have hF : MeasurableSet F := by
    have hr : Measurable (fun (ℓ : ℕ → Fin m) (i : Fin n) => ℓ i) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    exact hr (Set.to_countable L).measurableSet
  have h := hM.indep.measure_inter_preimage_eq_mul E F hE hF
  exact h

theorem joint_law [IsProbabilityMeasure μ] (hlam : 0 < lam) {m : ℕ} {p : Fin m → ℝ}
    {J : ℕ → Ω → Fin m}
    (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (μ.restrict {ω | Ncount T t ω = n}).map
        (fun ω => ((fun i : Fin n => arrivalTime T (i + 1) ω), (fun i : Fin n => J i ω))) =
      ((Real.toNNReal (lam ^ n * Real.exp (-(lam * t)))) •
        volume.restrict (Osimp n t)).prod (Measure.pi (fun _ => cat p)) := by
  have hT := hM.arrivals
  have hS := Svec_measurable' hT.measurable n
  have hJv : Measurable (fun ω (i : Fin n) => J i ω) :=
    measurable_pi_lambda _ (fun i => hM.label_measurable i)
  have hNm := Ncount_measurable' hT.measurable t (measurableSet_singleton n)
  refine (Measure.prod_eq fun s u hs hu => ?_).symm
  rw [Measure.map_apply (hS.prodMk hJv) (hs.prod hu), Measure.restrict_apply
    ((hS.prodMk hJv) (hs.prod hu))]
  have e : (fun ω => ((fun i : Fin n => arrivalTime T (i + 1) ω), (fun i : Fin n => J i ω))) ⁻¹'
      (s ×ˢ u) ∩ {ω | Ncount T t ω = n} =
      ({ω | Ncount T t ω = n} ∩ {ω | (fun i : Fin n => arrivalTime T (i + 1) ω) ∈ s}) ∩
        {ω | (fun i : Fin n => J i ω) ∈ u} := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]; tauto
  rw [e, joint_indep hM t n hs u, os_all hlam hT ht n hs, ← map_Jvec hM n,
    Measure.map_apply hJv hu, Measure.smul_apply, Measure.restrict_apply hs]
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.ofReal]
  rfl

end WhittSplit


open MeasureTheory ProbabilityTheory Filter Topology QueueingFundamentals.Foundations

namespace WhittSplit

lemma snoc_mem_Osimp {n : ℕ} (x y : ℝ) (s : Fin n → ℝ) :
    (Fin.snoc s y : Fin (n + 1) → ℝ) ∈ Osimp (n + 1) x ↔ (0 < y ∧ y < x) ∧ s ∈ Osimp n y := by
  simp only [Osimp, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hm, hb⟩
    have hy := hb (Fin.last n)
    simp only [Fin.snoc_last] at hy
    refine ⟨hy, fun i j hij => ?_, fun i => ?_⟩
    · have := hm (Fin.castSucc_lt_castSucc_iff.mpr hij)
      simpa [Fin.snoc_castSucc] using this
    · have h1 := hb (Fin.castSucc i)
      have h2 := hm (Fin.castSucc_lt_last i)
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at h1 h2
      exact ⟨h1.1, h2⟩
  · rintro ⟨⟨hy0, hyx⟩, hm, hb⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · induction j using Fin.lastCases with
      | last =>
        induction i using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast i => simpa [Fin.snoc_castSucc, Fin.snoc_last] using (hb i).2
      | cast j =>
        induction i using Fin.lastCases with
        | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last j).le)
        | cast i =>
          have : i < j := Fin.castSucc_lt_castSucc_iff.mp hij
          simpa [Fin.snoc_castSucc] using hm this
    · induction i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using ⟨hy0, hyx⟩
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact ⟨(hb i).1, lt_trans (hb i).2 hyx⟩

lemma Osimp_subset_Icc (n : ℕ) (x : ℝ) :
    Osimp n x ⊆ Set.Icc (fun _ => (0 : ℝ)) (fun _ => x) := by
  intro s hs
  exact ⟨fun i => (hs.2 i).1.le, fun i => (hs.2 i).2.le⟩

lemma volume_Osimp_lt_top (n : ℕ) (x : ℝ) : volume (Osimp n x) < ⊤ :=
  lt_of_le_of_lt (measure_mono (Osimp_subset_Icc n x)) isCompact_Icc.measure_lt_top

lemma integrableOn_bdd {α : Type*} [MeasurableSpace α] {ν : Measure α} {s : Set α}
    (hs : ν s < ⊤) {f : α → ℂ} (hf : Measurable f) (hb : ∀ a, ‖f a‖ ≤ 1) :
    IntegrableOn f s ν := by
  haveI : IsFiniteMeasure (ν.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs⟩
  exact Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hb)

lemma intervalIntegrable_bdd {φ : ℝ → ℂ} (hφm : Measurable φ) (hφb : ∀ x, ‖φ x‖ ≤ 1)
    (a b : ℝ) : IntervalIntegrable φ volume a b := by
  refine ⟨integrableOn_bdd measure_Ioc_lt_top hφm hφb,
    integrableOn_bdd measure_Ioc_lt_top hφm hφb⟩

theorem simplex_integral (φ : ℝ → ℂ) (hφm : Measurable φ) (hφb : ∀ x, ‖φ x‖ ≤ 1)
    (D : Finset ℝ) (hφc : ∀ x, x ∉ D → ContinuousAt φ x) (n : ℕ) :
    ∀ x : ℝ, 0 ≤ x → ∫ s in Osimp n x, ∏ j, φ (s j) =
      (∫ y in (0 : ℝ)..x, φ y) ^ n / (n.factorial : ℂ) := by
  have hII := intervalIntegrable_bdd hφm hφb
  set Φ : ℝ → ℂ := fun y => ∫ u in (0 : ℝ)..y, φ u with hΦ
  have hprodm : ∀ k : ℕ, Measurable (fun s : Fin k → ℝ => ∏ j, φ (s j)) := fun k =>
    Finset.measurable_prod _ (fun j _ => hφm.comp (measurable_pi_apply j))
  have hprodb : ∀ k : ℕ, ∀ s : Fin k → ℝ, ‖∏ j, φ (s j)‖ ≤ 1 := by
    intro k s
    rw [norm_prod]
    exact Finset.prod_le_one (fun j _ => norm_nonneg _) (fun j _ => hφb _)
  induction n with
  | zero =>
    intro x _
    have hO : Osimp 0 x = Set.univ := by
      ext s; simp only [Osimp, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨fun a => Fin.elim0 a, fun i => Fin.elim0 i⟩
    have hv : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
      rw [volume_pi, Measure.pi_of_empty]; simp
    simp only [Finset.univ_eq_empty, Finset.prod_empty, integral_const, hO, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, Measure.restrict_univ]
    rw [measureReal_def, hv]
    simp
  | succ n ih =>
    intro x hx
    set F : (Fin (n + 1) → ℝ) → ℂ := (Osimp (n + 1) x).indicator (fun s => ∏ j, φ (s j))
    have hFint : Integrable F := by
      have := integrableOn_bdd (volume_Osimp_lt_top (n + 1) x) (hprodm (n + 1)) (hprodb (n + 1))
      exact (integrable_indicator_iff (measurableSet_Osimp _ _)).2 this
    rw [← integral_indicator (measurableSet_Osimp _ _)]
    have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ))
      (Fin.last n)
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
    have hG : ∀ z : ℝ × (Fin n → ℝ), F (e.symm z) =
        (Set.Ioo 0 x).indicator φ z.1 *
          (Osimp n z.1).indicator (fun s => ∏ j, φ (s j)) z.2 := by
      rintro ⟨y, s⟩
      have hes : e.symm (y, s) = Fin.snoc s y := by
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_last']
      simp only [F, hes]
      by_cases hmem : (Fin.snoc s y : Fin (n + 1) → ℝ) ∈ Osimp (n + 1) x
      · rw [Set.indicator_of_mem hmem]
        obtain ⟨h1, h2⟩ := (snoc_mem_Osimp x y s).1 hmem
        rw [Set.indicator_of_mem (show y ∈ Set.Ioo 0 x from h1), Set.indicator_of_mem h2,
          Fin.prod_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        ring
      · rw [Set.indicator_of_notMem hmem]
        rw [snoc_mem_Osimp] at hmem
        by_cases h1 : y ∈ Set.Ioo 0 x
        · rw [Set.indicator_of_notMem (fun h => hmem ⟨h1, h⟩), mul_zero]
        · rw [Set.indicator_of_notMem h1, zero_mul]
    have hvol : (volume : Measure (Fin (n + 1) → ℝ)) =
        Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ)) := volume_pi
    have e1 : ∫ s, F s = ∫ z, F (e.symm z) ∂((volume : Measure ℝ).prod
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) := by
      rw [mp.symm.integral_comp' F]
      rfl
    have hGint : Integrable (fun z => F (e.symm z)) ((volume : Measure ℝ).prod
        (Measure.pi fun _ : Fin n => (volume : Measure ℝ))) := by
      have := (mp.symm.integrable_comp_emb e.symm.measurableEmbedding (g := F)).2 hFint
      exact this
    rw [e1, integral_prod _ hGint]
    simp_rw [hG]
    have e2 : ∀ y : ℝ, ∫ s, (Set.Ioo 0 x).indicator φ y *
        (Osimp n y).indicator (fun s => ∏ j, φ (s j)) s ∂(Measure.pi fun _ : Fin n => volume) =
        (Set.Ioo 0 x).indicator (fun y => φ y * (Φ y ^ n / (n.factorial : ℂ))) y := by
      intro y
      rw [integral_const_mul]
      by_cases hy : y ∈ Set.Ioo 0 x
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        congr 1
        have := ih y hy.1.le
        rw [← this, integral_indicator (measurableSet_Osimp _ _)]
        rfl
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
    simp_rw [e2]
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hx]
    -- FTC
    have hΦc : Continuous Φ := intervalIntegral.continuous_primitive hII 0
    have hderiv : ∀ y ∈ Set.Ioo 0 x \ (D : Set ℝ),
        HasDerivAt (fun y => Φ y ^ (n + 1) / ((n + 1).factorial : ℂ))
          (φ y * (Φ y ^ n / (n.factorial : ℂ))) y := by
      intro y hy
      have hd : HasDerivAt Φ (φ y) y :=
        intervalIntegral.integral_hasDerivAt_right (hII 0 y)
          (hφm.stronglyMeasurable.stronglyMeasurableAtFilter) (hφc y hy.2)
      have := (hd.fun_pow (n + 1)).div_const ((n + 1).factorial : ℂ)
      refine this.congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      rw [Nat.factorial_succ]
      push_cast
      have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      field_simp
    have hint : IntervalIntegrable (fun y => φ y * (Φ y ^ n / (n.factorial : ℂ))) volume 0 x :=
      (hII 0 x).mul_continuousOn ((hΦc.pow n).div_const _).continuousOn
    rw [integral_eq_of_hasDerivAt_off_countable_of_le _ _ hx D.countable_toSet
      (((hΦc.pow (n + 1)).div_const _).continuousOn) hderiv hint]
    simp [Φ]

end WhittSplit


open MeasureTheory ProbabilityTheory Filter Topology QueueingFundamentals.Foundations

namespace WhittSplit

/-- class-window weight: `w ℓ` if `s ∈ (a ℓ, b ℓ]`, else `1` -/
noncomputable def gw {m : ℕ} (a b : Fin m → ℝ) (w : Fin m → ℂ) (s : ℝ) (ℓ : Fin m) : ℂ :=
  if a ℓ < s ∧ s ≤ b ℓ then w ℓ else 1

/-- label-averaged weight -/
noncomputable def gbar {m : ℕ} (p a b : Fin m → ℝ) (w : Fin m → ℂ) (s : ℝ) : ℂ :=
  ∑ i, (p i : ℂ) * gw a b w s i

lemma gw_eq {m : ℕ} (a b : Fin m → ℝ) (w : Fin m → ℂ) (s : ℝ) (ℓ : Fin m) :
    gw a b w s ℓ = (Set.Ioc (a ℓ) (b ℓ)).indicator (fun _ => w ℓ - 1) s + 1 := by
  unfold gw
  by_cases h : a ℓ < s ∧ s ≤ b ℓ
  · rw [if_pos h, Set.indicator_of_mem (show s ∈ Set.Ioc (a ℓ) (b ℓ) from h)]; ring
  · rw [if_neg h, Set.indicator_of_notMem (show s ∉ Set.Ioc (a ℓ) (b ℓ) from h)]; ring

lemma gw_measurable {m : ℕ} (a b : Fin m → ℝ) (w : Fin m → ℂ) (ℓ : Fin m) :
    Measurable (fun s => gw a b w s ℓ) := by
  unfold gw
  exact Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
    (measurableSet_le measurable_id measurable_const)) measurable_const measurable_const

lemma norm_gw {m : ℕ} (a b : Fin m → ℝ) (w : Fin m → ℂ) (hw : ∀ i, ‖w i‖ = 1) (s : ℝ)
    (ℓ : Fin m) : ‖gw a b w s ℓ‖ = 1 := by
  unfold gw; split_ifs <;> simp [hw]

lemma gbar_measurable {m : ℕ} (p a b : Fin m → ℝ) (w : Fin m → ℂ) :
    Measurable (gbar p a b w) := by
  unfold gbar
  exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (gw_measurable a b w i))

lemma norm_gbar {m : ℕ} (p a b : Fin m → ℝ) (w : Fin m → ℂ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hw : ∀ i, ‖w i‖ = 1) (s : ℝ) : ‖gbar p a b w s‖ ≤ 1 := by
  unfold gbar
  calc ‖∑ i, (p i : ℂ) * gw a b w s i‖ ≤ ∑ i, ‖(p i : ℂ) * gw a b w s i‖ := norm_sum_le _ _
    _ = ∑ i, p i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [norm_mul, norm_gw a b w hw, mul_one, Complex.norm_real, Real.norm_of_nonneg (hp i)]
    _ = 1 := hp1

lemma gw_continuousAt {m : ℕ} (a b : Fin m → ℝ) (w : Fin m → ℂ) (ℓ : Fin m) (s : ℝ)
    (ha : s ≠ a ℓ) (hb : s ≠ b ℓ) : ContinuousAt (fun s => gw a b w s ℓ) s := by
  unfold gw
  by_cases h : a ℓ < s ∧ s ≤ b ℓ
  · have hs : s < b ℓ := lt_of_le_of_ne h.2 hb
    have : ∀ᶠ u in 𝓝 s, (if a ℓ < u ∧ u ≤ b ℓ then w ℓ else 1) = w ℓ := by
      filter_upwards [Ioo_mem_nhds h.1 hs] with u hu
      rw [if_pos ⟨hu.1, hu.2.le⟩]
    exact (continuousAt_congr this).2 continuousAt_const
  · have : ∀ᶠ u in 𝓝 s, (if a ℓ < u ∧ u ≤ b ℓ then w ℓ else 1) = 1 := by
      rcases not_and_or.1 h with h1 | h1
      · push_neg at h1
        have h1' : s < a ℓ := lt_of_le_of_ne h1 ha
        filter_upwards [Iio_mem_nhds h1'] with u hu
        rw [if_neg (fun hh => absurd hh.1 (not_lt.2 (le_of_lt hu)))]
      · push_neg at h1
        filter_upwards [Ioi_mem_nhds h1] with u hu
        rw [if_neg (fun hh => absurd hh.2 (not_le.2 hu))]
    exact (continuousAt_congr this).2 continuousAt_const

lemma gbar_continuousAt {m : ℕ} (p a b : Fin m → ℝ) (w : Fin m → ℂ) (s : ℝ)
    (hs : s ∉ (Finset.univ.image a ∪ Finset.univ.image b)) :
    ContinuousAt (gbar p a b w) s := by
  unfold gbar
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, not_or,
    not_exists] at hs
  refine tendsto_finsetSum _ (fun i _ => ContinuousAt.mul continuousAt_const ?_)
  exact gw_continuousAt a b w i s (fun h => hs.1 i h.symm) (fun h => hs.2 i h.symm)

lemma intervalIntegrable_bddM {φ : ℝ → ℂ} (hφm : Measurable φ) (M : ℝ) (hφb : ∀ x, ‖φ x‖ ≤ M)
    (a b : ℝ) : IntervalIntegrable φ volume a b := by
  have h : ∀ s : Set ℝ, volume s < ⊤ → IntegrableOn φ s volume := by
    intro s hs
    haveI : IsFiniteMeasure (volume.restrict s) := ⟨by rw [Measure.restrict_apply_univ]; exact hs⟩
    exact Integrable.of_bound hφm.aestronglyMeasurable M (Eventually.of_forall hφb)
  exact ⟨h _ measure_Ioc_lt_top, h _ measure_Ioc_lt_top⟩

lemma integral_ind_Ioc (a b c Bt : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Bt) (z : ℂ) :
    ∫ s in (0 : ℝ)..Bt, (Set.Ioc a b).indicator (fun _ => z) s = ((b - a : ℝ) : ℂ) * z := by
  have hB : 0 ≤ Bt := le_trans (le_trans ha hab) hb
  rw [intervalIntegral.integral_of_le hB, setIntegral_indicator measurableSet_Ioc]
  have : Set.Ioc 0 Bt ∩ Set.Ioc a b = Set.Ioc a b := by
    apply Set.inter_eq_right.mpr
    intro x hx; exact ⟨lt_of_le_of_lt ha hx.1, le_trans hx.2 hb⟩
  rw [this, setIntegral_const, Real.volume_real_Ioc_of_le hab, Complex.real_smul]

lemma integral_gbar {m : ℕ} (p a b : Fin m → ℝ) (w : Fin m → ℂ) (Bt : ℝ)
    (hab : ∀ i, 0 ≤ a i ∧ a i ≤ b i) (hbB : ∀ i, b i ≤ Bt) (hp1 : ∑ i, p i = 1)
    (hw : ∀ i, ‖w i‖ = 1) :
    ∫ s in (0 : ℝ)..Bt, gbar p a b w s =
      Bt + ∑ i, (p i : ℂ) * ((b i - a i : ℝ) * (w i - 1)) := by
  unfold gbar
  rw [intervalIntegral.integral_finset_sum (fun i _ =>
    (intervalIntegrable_bdd (gw_measurable a b w i) (fun s => (norm_gw a b w hw s i).le)
      0 Bt).const_mul _)]
  have hterm : ∀ i, ∫ s in (0 : ℝ)..Bt, (p i : ℂ) * gw a b w s i =
      (p i : ℂ) * (((b i - a i : ℝ) : ℂ) * (w i - 1) + Bt) := by
    intro i
    rw [intervalIntegral.integral_const_mul]
    congr 1
    simp_rw [gw_eq]
    have hii : IntervalIntegrable ((Set.Ioc (a i) (b i)).indicator fun _ => w i - 1) volume 0 Bt :=
      intervalIntegrable_bddM (Measurable.indicator measurable_const measurableSet_Ioc)
        ‖w i - 1‖ (fun s => by
          by_cases h : s ∈ Set.Ioc (a i) (b i)
          · rw [Set.indicator_of_mem h]
          · rw [Set.indicator_of_notMem h]; simp) 0 Bt
    rw [intervalIntegral.integral_add hii intervalIntegrable_const,
      integral_ind_Ioc _ _ 0 _ (hab i).1 (hab i).2 (hbB i)]
    simp
  simp_rw [hterm]
  rw [show (∑ i, (p i : ℂ) * (((b i - a i : ℝ) : ℂ) * (w i - 1) + Bt)) =
      (∑ i, (p i : ℂ)) * Bt + ∑ i, (p i : ℂ) * (((b i - a i : ℝ) : ℂ) * (w i - 1)) by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => by ring)]
  rw [← Complex.ofReal_sum, hp1]
  simp

end WhittSplit


open MeasureTheory ProbabilityTheory Filter Topology QueueingFundamentals.Foundations

namespace WhittSplit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {lam : ℝ} {T : ℕ → Ω → ℝ}

lemma p_nonneg {m : ℕ} {p : Fin m → ℝ} {J : ℕ → Ω → Fin m}
    (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J) (i : Fin m) : 0 ≤ p i := by
  rw [← hM.label_law 0 i]; exact measureReal_nonneg

lemma p_sum [IsProbabilityMeasure μ] {m : ℕ} {p : Fin m → ℝ} {J : ℕ → Ω → Fin m}
    (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J) : ∑ i, p i = 1 := by
  have h1 : (μ.map (J 0)) Set.univ = 1 := by
    rw [Measure.map_apply (hM.label_measurable 0) MeasurableSet.univ]; simp
  rw [map_J hM 0] at h1
  simp only [cat, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one] at h1
  have := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)] at this
  simpa [ENNReal.toReal_ofReal (p_nonneg hM _)] using this

lemma cat_real_singleton {m : ℕ} {p : Fin m → ℝ} (hp : ∀ i, 0 ≤ p i) (i : Fin m) :
    (cat p).real {i} = p i := by
  rw [measureReal_def, cat_singleton, ENNReal.toReal_ofReal (hp i)]

lemma integral_cat {m : ℕ} {p : Fin m → ℝ} (hp : ∀ i, 0 ≤ p i) (f : Fin m → ℂ) :
    ∫ ℓ, f ℓ ∂(cat p) = ∑ i, (p i : ℂ) * f i := by
  rw [integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cat_real_singleton hp, Complex.real_smul]

lemma gwpair_measurable {m : ℕ} (a b : Fin m → ℝ) (w : Fin m → ℂ) {n : ℕ} (j : Fin n) :
    Measurable (fun z : (Fin n → ℝ) × (Fin n → Fin m) => gw a b w (z.1 j) (z.2 j)) := by
  have h2 : Measurable (fun z : (Fin n → ℝ) × (Fin n → Fin m) => z.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  have h1 : Measurable (fun z : (Fin n → ℝ) × (Fin n → Fin m) => z.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  unfold gw
  refine Measurable.ite ?_ ((measurable_of_countable w).comp h2) measurable_const
  exact (measurableSet_lt ((measurable_of_countable a).comp h2) h1).inter
    (measurableSet_le h1 ((measurable_of_countable b).comp h2))

theorem term_integral [IsProbabilityMeasure μ] (hlam : 0 < lam) {m : ℕ} {p : Fin m → ℝ}
    {J : ℕ → Ω → Fin m} (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J)
    {t : ℝ} (ht : 0 < t) (a b : Fin m → ℝ) (w : Fin m → ℂ) (hw : ∀ i, ‖w i‖ = 1) (n : ℕ) :
    ∫ ω in {ω | Ncount T t ω = n}, ∏ j : Fin n, gw a b w (arrivalTime T (j + 1) ω) (J j ω) ∂μ =
      ((lam ^ n * Real.exp (-(lam * t)) : ℝ) : ℂ) *
        ((∫ s in (0 : ℝ)..t, gbar p a b w s) ^ n / (n.factorial : ℂ)) := by
  have hT := hM.arrivals
  have hp := p_nonneg hM
  have hp1 := p_sum hM
  have hS := Svec_measurable' hT.measurable n
  have hJv : Measurable (fun ω (i : Fin n) => J i ω) :=
    measurable_pi_lambda _ (fun i => hM.label_measurable i)
  set H : (Fin n → ℝ) × (Fin n → Fin m) → ℂ := fun z => ∏ j, gw a b w (z.1 j) (z.2 j) with hH
  have hHm : Measurable H := Finset.measurable_prod _ (fun j _ => gwpair_measurable a b w j)
  have hHb : ∀ z, ‖H z‖ ≤ 1 := by
    intro z
    simp only [hH, norm_prod, norm_gw a b w hw, Finset.prod_const_one, le_refl]
  have e1 : ∫ ω in {ω | Ncount T t ω = n}, ∏ j : Fin n, gw a b w (arrivalTime T (j + 1) ω) (J j ω) ∂μ
      = ∫ z, H z ∂((μ.restrict {ω | Ncount T t ω = n}).map
        (fun ω => ((fun i : Fin n => arrivalTime T (i + 1) ω), (fun i : Fin n => J i ω)))) := by
    rw [integral_map (hS.prodMk hJv).aemeasurable hHm.aestronglyMeasurable]
  rw [e1, joint_law hlam hM ht n]
  set c := Real.toNNReal (lam ^ n * Real.exp (-(lam * t)))
  haveI : IsFiniteMeasure (volume.restrict (Osimp n t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_Osimp_lt_top n t⟩
  have hint : Integrable H ((c • volume.restrict (Osimp n t)).prod (Measure.pi fun _ => cat p)) :=
    Integrable.of_bound hHm.aestronglyMeasurable 1 (Eventually.of_forall hHb)
  rw [integral_prod H hint, integral_smul_nnreal_measure]
  have hinner : ∀ s : Fin n → ℝ, ∫ ℓ, H (s, ℓ) ∂(Measure.pi fun _ => cat p) =
      ∏ j, gbar p a b w (s j) := by
    intro s
    simp only [hH]
    rw [integral_fintype_prod_eq_prod (fun j ℓj => gw a b w (s j) ℓj)]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [integral_cat hp]
    rfl
  simp_rw [hinner]
  set D : Finset ℝ := Finset.univ.image a ∪ Finset.univ.image b
  rw [simplex_integral (gbar p a b w) (gbar_measurable p a b w) (norm_gbar p a b w hp hp1 hw)
    D (fun x hx => gbar_continuousAt p a b w x hx) n t ht.le]
  rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), Complex.real_smul]

end WhittSplit


open MeasureTheory ProbabilityTheory Filter Topology QueueingFundamentals.Foundations

namespace WhittSplit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {lam : ℝ} {T : ℕ → Ω → ℝ}

lemma pathwise_prod {m : ℕ} {J : ℕ → Ω → Fin m} (a b : Fin m → ℝ) (w : Fin m → ℂ) {Bt : ℝ}
    (hbB : ∀ i, b i ≤ Bt) {ω : Ω} (hω : ∀ k, 0 ≤ T k ω) (n : ℕ)
    (h1 : arrivalTime T n ω ≤ Bt) (h2 : Bt < arrivalTime T (n + 1) ω) :
    ∏ i, w i ^ (WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω) =
      ∏ j : Fin n, gw a b w (arrivalTime T (j + 1) ω) (J j ω) := by
  classical
  have hset : ∀ i, {k : ℕ | J k ω = i ∧ a i < arrivalTime T (k + 1) ω ∧
      arrivalTime T (k + 1) ω ≤ b i} =
      ↑((Finset.range n).filter (fun k => J k ω = i ∧ a i < arrivalTime T (k + 1) ω ∧
        arrivalTime T (k + 1) ω ≤ b i)) := by
    intro i
    ext k
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · intro hk
      refine ⟨?_, hk⟩
      by_contra hkn
      push_neg at hkn
      have := psum_mono hω (show n + 1 ≤ k + 1 by omega)
      linarith [hk.2.2, hbB i]
    · exact fun h => h.2
  have hC : ∀ i, WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω =
      ((Finset.range n).filter (fun k => J k ω = i ∧ a i < arrivalTime T (k + 1) ω ∧
        arrivalTime T (k + 1) ω ≤ b i)).card := by
    intro i
    unfold WhittEfficiency.IS.classWindowCount
    rw [hset i, Set.ncard_coe_finset]
  simp_rw [hC]
  rw [Fin.prod_univ_eq_prod_range (fun k => gw a b w (arrivalTime T (k + 1) ω) (J k ω)) n]
  have : ∀ i, w i ^ ((Finset.range n).filter (fun k => J k ω = i ∧ a i < arrivalTime T (k + 1) ω ∧
        arrivalTime T (k + 1) ω ≤ b i)).card =
      ∏ k ∈ Finset.range n, (if J k ω = i ∧ a i < arrivalTime T (k + 1) ω ∧
        arrivalTime T (k + 1) ω ≤ b i then w i else 1) := by
    intro i
    rw [← Finset.prod_filter, Finset.prod_const]
  simp_rw [this]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Finset.prod_eq_single (J k ω)]
  · simp only [true_and, gw]
  · intro i _ hi
    rw [if_neg (fun h => hi h.1.symm)]
  · simp

lemma classWindowCount_measurable {m : ℕ} {J : ℕ → Ω → Fin m} (hT : ∀ k, Measurable (T k))
    (hJ : ∀ k, Measurable (J k)) (i : Fin m) (a b : ℝ) :
    Measurable (WhittEfficiency.IS.classWindowCount T J i a b) := by
  have hA : ∀ k, Measurable (arrivalTime T k) := fun k => by
    unfold arrivalTime; exact Finset.measurable_sum _ (fun j _ => hT j)
  exact measurable_ncard_setOf _ (fun k => ((hJ k) (measurableSet_singleton i)).inter
    ((measurableSet_lt measurable_const (hA _)).inter (measurableSet_le (hA _) measurable_const)))

theorem pgf_formula [IsProbabilityMeasure μ] (hlam : 0 < lam) {m : ℕ} {p : Fin m → ℝ}
    {J : ℕ → Ω → Fin m} (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J)
    (a b : Fin m → ℝ) (hab : ∀ i, 0 ≤ a i ∧ a i ≤ b i) (w : Fin m → ℂ) (hw : ∀ i, ‖w i‖ = 1) :
    ∫ ω, ∏ i, w i ^ (WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω) ∂μ =
      Complex.exp (lam * ∑ i, (p i : ℂ) * ((b i - a i : ℝ) * (w i - 1))) := by
  have hT := hM.arrivals
  have hp1 := p_sum hM
  set Bt : ℝ := 1 + ∑ i, b i with hBt
  have hbB : ∀ i, b i ≤ Bt := by
    intro i
    have : b i ≤ ∑ j, b j :=
      Finset.single_le_sum (f := b) (fun j _ => le_trans (hab j).1 (hab j).2) (Finset.mem_univ i)
    linarith
  have hB0 : 0 < Bt := by
    have : 0 ≤ ∑ j, b j := Finset.sum_nonneg (fun j _ => le_trans (hab j).1 (hab j).2)
    linarith
  set f : Ω → ℂ := fun ω => ∏ i, w i ^ (WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω)
    with hf
  have hfm : Measurable f := by
    refine Finset.measurable_prod _ (fun i _ => ?_)
    exact (measurable_of_countable (fun k : ℕ => w i ^ k)).comp
      (classWindowCount_measurable hT.measurable hM.label_measurable i (a i) (b i))
  have hfb : ∀ ω, ‖f ω‖ ≤ 1 := by
    intro ω; simp [hf, norm_prod, hw]
  have hNm : ∀ n : ℕ, MeasurableSet {ω | Ncount T Bt ω = n} := fun n =>
    Ncount_measurable' hT.measurable Bt (measurableSet_singleton n)
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ => {ω | Ncount T Bt ω = n}) := by
    intro i j hij
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro ω h1 h2
    exact hij (h1.symm.trans h2)
  have hU : (⋃ n : ℕ, {ω | Ncount T Bt ω = n}) = Set.univ := by
    ext ω; simp
  have hfi : IntegrableOn f (⋃ n : ℕ, {ω | Ncount T Bt ω = n}) μ :=
    (Integrable.of_bound hfm.aestronglyMeasurable 1 (Eventually.of_forall hfb)).integrableOn
  have hsum := hasSum_integral_iUnion hNm hdisj hfi
  rw [hU, Measure.restrict_univ] at hsum
  set Φ : ℂ := ∫ s in (0 : ℝ)..Bt, gbar p a b w s
  have hterm : ∀ n : ℕ, ∫ ω in {ω | Ncount T Bt ω = n}, f ω ∂μ =
      ((lam ^ n * Real.exp (-(lam * Bt)) : ℝ) : ℂ) * (Φ ^ n / (n.factorial : ℂ)) := by
    intro n
    rw [← term_integral hlam hM hB0 a b w hw n]
    refine setIntegral_congr_ae (hNm n) ?_
    filter_upwards [gap_nonneg_ae hlam hT, finite_ae hlam hT hB0.le] with ω hω hK hn
    have := (count_iff hB0.le hω hK n).1 hn
    exact pathwise_prod a b w hbB hω n this.1 this.2
  simp_rw [hterm] at hsum
  have hexp := NormedSpace.expSeries_div_hasSum_exp ((lam : ℂ) * Φ)
  rw [← Complex.exp_eq_exp_ℂ] at hexp
  have hexp2 := hexp.mul_left (Complex.exp (-(lam * Bt : ℂ)))
  have heq : (fun n : ℕ => Complex.exp (-(lam * Bt : ℂ)) * ((lam : ℂ) * Φ) ^ n / (n.factorial : ℂ))
      = (fun n : ℕ => ((lam ^ n * Real.exp (-(lam * Bt)) : ℝ) : ℂ) *
        (Φ ^ n / (n.factorial : ℂ))) := by
    funext n
    push_cast
    ring
  simp_rw [mul_div_assoc'] at hexp2
  rw [heq] at hexp2
  rw [hsum.unique hexp2, ← Complex.exp_add]
  congr 1
  have hΦ : Φ = Bt + ∑ i, (p i : ℂ) * ((b i - a i : ℝ) * (w i - 1)) :=
    integral_gbar p a b w Bt hab hbB hp1 hw
  rw [hΦ]
  ring

end WhittSplit


open MeasureTheory ProbabilityTheory Filter Topology QueueingFundamentals.Foundations

namespace WhittSplit

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {lam : ℝ} {T : ℕ → Ω → ℝ}

lemma exp_mul_I_pow (x : ℝ) (k : ℕ) :
    Complex.exp (((k : ℝ) * x : ℝ) * Complex.I) = Complex.exp ((x : ℂ) * Complex.I) ^ k := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem split_main [IsProbabilityMeasure μ] (hlam : 0 < lam) {m : ℕ} {p : Fin m → ℝ}
    {J : ℕ → Ω → Fin m} (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J)
    (a b : Fin m → ℝ) (hab : ∀ i, 0 ≤ a i ∧ a i ≤ b i) :
    iIndepFun (fun i ω => WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω) μ ∧
    ∀ (i : Fin m) (k : ℕ),
      μ.real {ω | WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω = k} =
        Real.exp (-(lam * p i * (b i - a i))) * (lam * p i * (b i - a i)) ^ k / k.factorial := by
  have hT := hM.arrivals
  have hp := p_nonneg hM
  set C : Fin m → Ω → ℕ := fun i ω => WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω
    with hCdef
  have hCm : ∀ i, Measurable (C i) := fun i =>
    classWindowCount_measurable hT.measurable hM.label_measurable i (a i) (b i)
  set X : Fin m → Ω → ℝ := fun i ω => (C i ω : ℝ) with hXdef
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_from_nat.comp (hCm i)
  set ν : Fin m → NNReal := fun i => Real.toNNReal (lam * p i * (b i - a i)) with hνdef
  have hν : ∀ i, (ν i : ℝ) = lam * p i * (b i - a i) := fun i =>
    Real.coe_toNNReal _ (mul_nonneg (mul_nonneg hlam.le (hp i)) (by linarith [(hab i).2]))
  -- the pgf formula in exponential form
  have hpgf : ∀ w : Fin m → ℂ, (∀ i, ‖w i‖ = 1) →
      ∫ ω, ∏ i, w i ^ (C i ω) ∂μ = ∏ i, Complex.exp ((ν i : ℂ) * (w i - 1)) := by
    intro w hw
    rw [pgf_formula hlam hM a b hab w hw, ← Complex.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show ((ν i : ℝ) : ℂ) = ((lam * p i * (b i - a i) : ℝ) : ℂ) by rw [hν]]
    push_cast
    ring
  -- marginal characteristic functions
  have hmarg : ∀ i (s : ℝ), charFun (μ.map (X i)) s = charFun Po(ℝ, ν i) s := by
    intro i s
    rw [charFun_map_cast_poissonMeasure, charFun_apply, integral_map (hXm i).aemeasurable
      (by fun_prop)]
    classical
    set w : Fin m → ℂ := fun j => if j = i then Complex.exp ((s : ℂ) * Complex.I) else 1
    have hw : ∀ j, ‖w j‖ = 1 := by
      intro j; simp only [w]; split_ifs
      · exact Complex.norm_exp_ofReal_mul_I s
      · simp
    have h := hpgf w hw
    have e1 : ∀ ω, Complex.exp (((inner ℝ (X i ω) s : ℝ) : ℂ) * Complex.I) =
        ∏ j, w j ^ (C j ω) := by
      intro ω
      rw [Finset.prod_eq_single i (fun j _ hj => by simp [w, hj]) (by simp)]
      simp only [w, if_true, Real.inner_apply, hXdef]
      rw [exp_mul_I_pow]
    simp_rw [e1, h]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [w, hj]) (by simp)]
    simp [w]
  -- independence
  have hind : iIndepFun X μ := by
    rw [iIndepFun_iff_charFun_pi (fun i => (hXm i).aemeasurable)]
    intro t
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    have e1 : ∀ ω, Complex.exp (((inner ℝ (WithLp.toLp 2 (fun j => X j ω)) t : ℝ) : ℂ) *
        Complex.I) = ∏ j, Complex.exp (((t j : ℝ) : ℂ) * Complex.I) ^ (C j ω) := by
      intro ω
      rw [PiLp.inner_apply]
      simp only [PiLp.toLp_apply, Real.inner_apply, hXdef]
      push_cast
      rw [Finset.sum_mul, Complex.exp_sum]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [← exp_mul_I_pow]
      push_cast
      ring_nf
    simp_rw [e1]
    rw [hpgf _ (fun j => Complex.norm_exp_ofReal_mul_I _)]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [hmarg j, charFun_map_cast_poissonMeasure]
  refine ⟨?_, ?_⟩
  · have := hind.comp (fun _ x => Nat.floor x) (fun _ => Nat.measurable_floor)
    convert this using 1
    funext i ω
    simp [hXdef, Function.comp]
  · intro i k
    have hlaw : μ.map (X i) = Po(ℝ, ν i) := Measure.ext_of_charFun (funext (hmarg i))
    have e1 : {ω | WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω = k} =
        X i ⁻¹' {(k : ℝ)} := by
      ext ω; simp [hXdef, hCdef]
    rw [e1, ← map_measureReal_apply (hXm i) (measurableSet_singleton _), hlaw,
      map_measureReal_apply measurable_from_nat (measurableSet_singleton _)]
    have e2 : (Nat.cast : ℕ → ℝ) ⁻¹' {(k : ℝ)} = {k} := by
      ext n; simp
    rw [e2, poissonMeasure_real_singleton, hν]

end WhittSplit


open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    {m : ℕ} (p : Fin m → ℝ) (J : ℕ → Ω → Fin m)
    (hM : WhittEfficiency.IS.IsMarkedPoisson μ lam T p J)
    (a b : Fin m → ℝ) (hab : ∀ i, 0 ≤ a i ∧ a i ≤ b i) :
    iIndepFun (fun i ω => WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω) μ ∧
    ∀ (i : Fin m) (k : ℕ), μ.real {ω | WhittEfficiency.IS.classWindowCount T J i (a i) (b i) ω = k} =
      Real.exp (-(lam * p i * (b i - a i))) * (lam * p i * (b i - a i)) ^ k / k.factorial :=
  WhittSplit.split_main hlam hM a b hab
