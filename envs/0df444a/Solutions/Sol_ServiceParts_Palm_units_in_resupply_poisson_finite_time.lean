-- Prove2me | solution 1 for ServiceParts.Palm.units_in_resupply_poisson_finite_time
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:18:28.898544+00:00
-- url     : https://prove2.me/submissions/f1754b65-c03c-482a-ab27-09c0dd3bc40a

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology


namespace ServiceParts.Palm

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

/-- partial sums `gap 0 + ... + gap (m-1)` -/
noncomputable def psum (S : ResupplySystem Ω P) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range m, S.gap i ω

lemma psum_meas (S : ResupplySystem Ω P) (m : ℕ) : Measurable (psum S m) := by
  unfold psum
  exact Finset.measurable_sum _ (fun i _ => S.gap_measurable i)

lemma psum_indep [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (m : ℕ) :
    IndepFun (psum S m) (S.gap m) P := by
  have hmeas : ∀ i, Measurable (Sum.elim S.gap S.resupply i) := by
    rintro (k | k)
    · exact S.gap_measurable k
    · exact S.resupply_measurable k
  let A : Finset (ℕ ⊕ ℕ) := (Finset.range m).map (Function.Embedding.inl (β := ℕ))
  have hd : Disjoint A ({Sum.inl m} : Finset (ℕ ⊕ ℕ)) := by
    rw [Finset.disjoint_singleton_right]; simp [A]
  have := S.indep.indepFun_finset _ _ hd hmeas
  have hφ : Measurable (fun v : A → ℝ => ∑ i, v i) :=
    Finset.measurable_sum (f := fun (i : A) (v : A → ℝ) => v i) _ (fun i _ => measurable_pi_apply i)
  have hψ : Measurable (fun v : ({Sum.inl m} : Finset (ℕ ⊕ ℕ)) → ℝ =>
      v ⟨Sum.inl m, Finset.mem_singleton_self _⟩) := measurable_pi_apply _
  have h2 := this.comp hφ hψ
  convert h2 using 1
  · funext ω
    simp only [Function.comp_apply, psum]
    rw [Finset.sum_coe_sort A (fun i => Sum.elim S.gap S.resupply i ω), Finset.sum_map]
    rfl
  all_goals rfl

lemma psum_surv [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (m : ℕ) (s : ℝ) :
    P {ω | s < psum S m ω} = ENNReal.ofReal (surv S.rate m s) := by
  induction m generalizing s with
  | zero =>
    simp only [psum, Finset.range_zero, Finset.sum_empty, surv, Finset.sum_empty, mul_zero]
    split_ifs with h
    · simp [h]
    · simp [h]
  | succ m ih =>
    have e : {ω | s < psum S (m + 1) ω} = {ω | s < psum S m ω + S.gap m ω} := by
      ext ω; simp [psum, Finset.sum_range_succ]
    rw [e, step_law (psum_meas S m) (S.gap_measurable m) (psum_indep S m) S.rate_pos
      (S.gap_law m) (surv S.rate m) (surv_meas _ _) (surv_nonneg S.rate_pos m)
      (surv_le_one S.rate_pos m) ih s, surv_integral S.rate_pos]


lemma arrival_eq (S : ResupplySystem Ω P) (k : ℕ) (ω : Ω) : S.arrival k ω = psum S (k + 1) ω := rfl

lemma psum_mono (S : ResupplySystem Ω P) {ω : Ω} (hω : ∀ k, 0 ≤ S.gap k ω) {i j : ℕ}
    (hij : i ≤ j) : psum S i ω ≤ psum S j ω := by
  unfold psum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hij)
    (fun k _ _ => hω k)

lemma count_iff (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 ≤ t) {ω : Ω}
    (hω : ∀ k, 0 ≤ S.gap k ω) (hK : ∃ K, t < psum S K ω) (n : ℕ) :
    S.orderCount t ω = n ↔ psum S n ω ≤ t ∧ t < psum S (n + 1) ω := by
  obtain ⟨K, hK⟩ := hK
  have hfin : {k : ℕ | S.arrival k ω ≤ t}.Finite := by
    refine (Finset.finite_toSet (Finset.range K)).subset (fun k hk => ?_)
    simp only [Set.mem_setOf_eq, arrival_eq] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h; push_neg at h
    have := psum_mono S hω (show K ≤ k + 1 by omega)
    linarith
  unfold ResupplySystem.orderCount
  constructor
  · intro hc
    by_contra hneg
    rw [not_and_or, not_le, not_lt] at hneg
    rcases hneg with h | h
    · have hn : 1 ≤ n := by
        by_contra h0; push_neg at h0
        have : n = 0 := by omega
        subst this; simp [psum] at h; linarith
      have hsub : {k : ℕ | S.arrival k ω ≤ t} ⊆ ↑(Finset.range (n - 1)) := by
        intro k hk
        simp only [Set.mem_setOf_eq, arrival_eq] at hk
        simp only [Finset.coe_range, Set.mem_Iio]
        by_contra h'; push_neg at h'
        have := psum_mono S hω (show n ≤ k + 1 by omega)
        linarith
      have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset, Finset.card_range, hc] at this
      omega
    · have hsub : (↑(Finset.range (n + 1)) : Set ℕ) ⊆ {k : ℕ | S.arrival k ω ≤ t} := by
        intro k hk
        simp only [Finset.coe_range, Set.mem_Iio] at hk
        simp only [Set.mem_setOf_eq, arrival_eq]
        have := psum_mono S hω (show k + 1 ≤ n + 1 by omega)
        linarith
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset, Finset.card_range, hc] at this
      omega
  · rintro ⟨h1, h2⟩
    have : {k : ℕ | S.arrival k ω ≤ t} = ↑(Finset.range n) := by
      ext k
      simp only [Set.mem_setOf_eq, arrival_eq, Finset.coe_range, Set.mem_Iio]
      constructor
      · intro hk; by_contra h'; push_neg at h'
        have := psum_mono S hω (show n + 1 ≤ k + 1 by omega)
        linarith
      · intro hk
        have := psum_mono S hω (show k + 1 ≤ n by omega)
        linarith
    rw [this, Set.ncard_coe_finset, Finset.card_range]

lemma gap_nonneg_ae [IsProbabilityMeasure P] (S : ResupplySystem Ω P) :
    ∀ᵐ ω ∂P, ∀ k, 0 ≤ S.gap k ω := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have : {ω | ¬ 0 ≤ S.gap k ω} = S.gap k ⁻¹' Set.Iio 0 := by ext; simp
  rw [this, ← Measure.map_apply (S.gap_measurable k) measurableSet_Iio, S.gap_law k]
  haveI := isProbabilityMeasure_expMeasure S.rate_pos
  refine le_antisymm ?_ bot_le
  calc expMeasure S.rate (Set.Iio 0) ≤ expMeasure S.rate (Set.Iic 0) :=
        measure_mono Set.Iio_subset_Iic_self
    _ = ENNReal.ofReal (cdf (expMeasure S.rate) 0) := (ofReal_cdf _ _).symm
    _ = 0 := by rw [cdf_expMeasure_eq S.rate_pos, if_pos le_rfl]; simp

lemma surv_tendsto {r : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m => surv r m t) atTop (𝓝 1) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (r * t)).tendsto_sum_nat
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.const_mul (Real.exp (-(r * t)))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  refine h2.congr (fun m => ?_)
  rw [surv, if_neg (not_lt.2 ht)]

lemma finite_ae [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∃ K, t < psum S K ω := by
  rw [ae_iff]
  have hb : ∀ m, (P {ω | ¬ ∃ K, t < psum S K ω}).toReal ≤ 1 - surv S.rate m t := by
    intro m
    have hsub : {ω | ¬ ∃ K, t < psum S K ω} ⊆ {ω | t < psum S m ω}ᶜ := by
      intro ω hω h; exact hω ⟨m, h⟩
    have hms : MeasurableSet {ω | t < psum S m ω} :=
      measurableSet_lt measurable_const (psum_meas S m)
    calc (P {ω | ¬ ∃ K, t < psum S K ω}).toReal ≤ (P {ω | t < psum S m ω}ᶜ).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ = 1 - surv S.rate m t := by
          rw [prob_compl_eq_one_sub hms, psum_surv,
            ENNReal.toReal_sub_of_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (surv_le_one S.rate_pos m t)) ENNReal.one_ne_top,
            ENNReal.toReal_ofReal (surv_nonneg S.rate_pos m t)]
          simp
  have hlim : Tendsto (fun m => 1 - surv S.rate m t) atTop (𝓝 0) := by
    have := (surv_tendsto (r := S.rate) ht).const_sub 1
    simpa using this
  have h0 := ge_of_tendsto' hlim hb
  have h1 : (P {ω | ¬ ∃ K, t < psum S K ω}).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
  rwa [ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h1

theorem order_count_core [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t)
    (n : ℕ) :
    (P {ω | S.orderCount t ω = n}).toReal =
      Real.exp (-(S.rate * t)) * (S.rate * t) ^ n / (Nat.factorial n : ℝ) := by
  set A := {ω | t < psum S (n + 1) ω}
  set C := {ω | t < psum S n ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (psum_meas S _)
  have hC : MeasurableSet C := measurableSet_lt measurable_const (psum_meas S _)
  have e1 : P {ω | S.orderCount t ω = n} = P (A \ C) := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [gap_nonneg_ae S, finite_ae S ht.le] with ω hω hK
    show S.orderCount t ω = n ↔ ω ∈ A \ C
    rw [count_iff S ht.le hω hK n]
    simp only [A, C, Set.mem_diff, Set.mem_setOf_eq, not_lt]
    tauto
  have e2 : P (A ∩ C) = P C := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [gap_nonneg_ae S] with ω hω
    simp only [A, C, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨lt_of_lt_of_le h (psum_mono S hω (Nat.le_succ n)), h⟩
  have e3 := measure_inter_add_diff (μ := P) A hC
  rw [e2] at e3
  have e4 : P (A \ C) = P A - P C := by
    rw [← e3, ENNReal.add_sub_cancel_left (measure_ne_top _ _)]
  have hle : P C ≤ P A := by rw [← e3]; exact le_add_right le_rfl
  rw [e1, e4, ENNReal.toReal_sub_of_le hle (measure_ne_top _ _), psum_surv, psum_surv,
    ENNReal.toReal_ofReal (surv_nonneg S.rate_pos _ _),
    ENNReal.toReal_ofReal (surv_nonneg S.rate_pos _ _), surv, surv, if_neg (not_lt.2 ht.le),
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

theorem os_succ [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (m : ℕ)
    {A : Set (Fin (m + 1) → ℝ)} (hA : MeasurableSet A) :
    P ({ω | S.orderCount t ω = m + 1} ∩ {ω | (fun i : Fin (m + 1) => S.arrival i ω) ∈ A}) =
      ENNReal.ofReal (S.rate ^ (m + 1) * Real.exp (-(S.rate * t))) *
        volume (A ∩ {x : Fin (m + 1) → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t}) := by
  set O := {x : Fin (m + 1) → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t} with hO
  set r := S.rate with hr_def
  have hr : 0 < r := S.rate_pos
  let gv : Ω → (Fin (m + 1) → ℝ) := fun ω i => S.gap i ω
  have hgv : Measurable gv := measurable_pi_lambda _ (fun i => S.gap_measurable i)
  have harr : ∀ ω, (fun i : Fin (m + 1) => S.arrival i ω) = Lmap (m + 1) (gv ω) := by
    intro ω; funext i
    rw [Lmap_apply]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range] at hk
    simp only [extv, dif_pos (show k < m + 1 by omega), gv]
  have hps : ∀ ω, psum S (m + 1) ω = ∑ i, gv ω i := by
    intro ω
    simp only [psum, gv]
    exact (Fin.sum_univ_eq_sum_range (fun k => S.gap k ω) (m + 1)).symm
  -- law of the gap vector
  have hI : iIndepFun (fun (i : Fin (m + 1)) ω => S.gap i ω) P :=
    S.indep.precomp (g := fun i : Fin (m + 1) => (Sum.inl i.val : ℕ ⊕ ℕ))
      (fun a b h => Fin.ext (Sum.inl_injective h))
  have hlaw : P.map gv = Measure.pi (fun _ : Fin (m + 1) => expMeasure r) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin (m + 1)) ω => S.gap i ω)
      (fun i : Fin (m + 1) => (S.gap_measurable i).aemeasurable)).1 hI]
    congr 1; funext i; exact S.gap_law i
  -- independence of the gap vector and the next gap
  have hind : IndepFun gv (S.gap (m + 1)) P := by
    have hmeas : ∀ i, Measurable (Sum.elim S.gap S.resupply i) := by
      rintro (k | k)
      · exact S.gap_measurable k
      · exact S.resupply_measurable k
    let A' : Finset (ℕ ⊕ ℕ) := (Finset.range (m + 1)).map (Function.Embedding.inl (β := ℕ))
    have hd : Disjoint A' ({Sum.inl (m + 1)} : Finset (ℕ ⊕ ℕ)) := by
      rw [Finset.disjoint_singleton_right]; simp [A']
    have h1 := S.indep.indepFun_finset _ _ hd hmeas
    have hmem : ∀ i : Fin (m + 1), (Sum.inl i.val : ℕ ⊕ ℕ) ∈ A' := by
      intro i; simp [A']; omega
    have hφ : Measurable (fun v : A' → ℝ => fun i : Fin (m + 1) => v ⟨Sum.inl i.val, hmem i⟩) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have hψ : Measurable (fun v : ({Sum.inl (m + 1)} : Finset (ℕ ⊕ ℕ)) → ℝ =>
        v ⟨Sum.inl (m + 1), Finset.mem_singleton_self _⟩) := measurable_pi_apply _
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
  have e1 : P ({ω | S.orderCount t ω = m + 1} ∩
      {ω | (fun i : Fin (m + 1) => S.arrival i ω) ∈ A}) =
      P ((fun ω => (gv ω, S.gap (m + 1) ω)) ⁻¹' W) := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [gap_nonneg_ae S, finite_ae S ht.le] with ω hω hK
    show (S.orderCount t ω = m + 1 ∧ (fun i : Fin (m + 1) => S.arrival i ω) ∈ A) ↔
      (Lmap (m + 1) (gv ω) ∈ A ∧ ∑ i, gv ω i ≤ t ∧ t < ∑ i, gv ω i + S.gap (m + 1) ω)
    rw [count_iff S ht.le hω hK, harr, ← hps]
    have : psum S (m + 1 + 1) ω = psum S (m + 1) ω + S.gap (m + 1) ω := by
      simp [psum, Finset.sum_range_succ]
    rw [this]
    tauto
  rw [e1, ← Measure.map_apply (hgv.prodMk (S.gap_measurable _)) hW,
    (indepFun_iff_map_prod_eq_prod_map_map hgv.aemeasurable
      (S.gap_measurable _).aemeasurable).1 hind, Measure.prod_apply hW, hlaw, S.gap_law,
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


theorem arrival_os_core [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t)
    (n : ℕ) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    P ({ω | S.orderCount t ω = n} ∩ {ω | (fun i : Fin n => S.arrival i ω) ∈ A}) =
      P {ω | S.orderCount t ω = n} *
        (ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n) *
          volume (A ∩ {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t})) := by
  cases n with
  | zero =>
    by_cases h : (fun i : Fin 0 => (0 : ℝ)) ∈ A
    · have hA' : A = Set.univ := by
        ext x; simp only [Set.mem_univ, iff_true]
        rwa [Subsingleton.elim x (fun i : Fin 0 => (0 : ℝ))]
      subst hA'
      have hsm : {x : Fin 0 → ℝ | StrictMono x} = Set.univ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro a; exact Fin.elim0 a
      have hv : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [volume_pi, Measure.pi_of_empty]; simp
      simp [hsm, hv]
    · have hA' : A = ∅ := by
        ext x; simp only [Set.mem_empty_iff_false, iff_false]
        rwa [Subsingleton.elim x (fun i : Fin 0 => (0 : ℝ))]
      subst hA'
      simp
  | succ m =>
    rw [os_succ S ht m hA, ← ENNReal.ofReal_toReal (measure_ne_top P {ω | S.orderCount t ω = m + 1}),
      order_count_core S ht, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (Real.exp_pos _).le
        (pow_nonneg (mul_nonneg S.rate_pos.le ht.le) _)) (Nat.cast_nonneg _))]
    congr 2
    have : (t : ℝ) ^ (m + 1) ≠ 0 := by positivity
    have : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-! ### Symmetrization over the simplex -/

lemma perm_mp {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → ℝ => x ∘ σ) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  convert h using 1
  funext x; funext i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

lemma measurableSet_strictMono {n : ℕ} :
    MeasurableSet {x : Fin n → ℝ | StrictMono x} := by
  have : {x : Fin n → ℝ | StrictMono x} = ⋂ i : Fin n, ⋂ j : Fin n, {x | i < j → x i < x j} := by
    ext x; simp [StrictMono]
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  by_cases h : i < j
  · simp only [h, true_implies]
    exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  · simp [h]

lemma measurableSet_box {n : ℕ} (t : ℝ) :
    MeasurableSet {x : Fin n → ℝ | ∀ i, 0 < x i ∧ x i < t} := by
  have : {x : Fin n → ℝ | ∀ i, 0 < x i ∧ x i < t} = Set.univ.pi (fun _ => Set.Ioo 0 t) := by
    ext x; simp
  rw [this]; exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

lemma injective_ae (n : ℕ) : ∀ᵐ x : Fin n → ℝ ∂volume, Function.Injective x := by
  have hsub : {x : Fin n → ℝ | ¬ Function.Injective x} ⊆
      ⋃ i : Fin n, ⋃ j : Fin n, ⋃ (_ : i ≠ j), {x | x i = x j} := by
    intro x hx
    simp only [Function.Injective, not_forall, Set.mem_setOf_eq] at hx
    obtain ⟨i, j, h1, h2⟩ := hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨i, j, h2, h1⟩
  rw [ae_iff]
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  let φ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i - LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have h := hyperplane_null φ 0 (Pi.single i 1) (by
    simp [φ, Pi.single_apply, hij.symm])
  refine measure_mono_null (fun x hx => ?_) h
  simp only [Set.mem_setOf_eq] at hx ⊢
  simp [φ, hx]

lemma sym_lintegral {n : ℕ} (t : ℝ) (f : (Fin n → ℝ) → ENNReal) (hf : Measurable f)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) x, f (x ∘ σ) = f x) :
    ∫⁻ x in {x : Fin n → ℝ | ∀ i, 0 < x i ∧ x i < t}, f x =
      (Nat.factorial n : ENNReal) *
        ∫⁻ x in {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t}, f x := by
  set Dl := {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t} with hDl
  set B := {x : Fin n → ℝ | ∀ i, 0 < x i ∧ x i < t} with hB
  have hDm : MeasurableSet Dl := measurableSet_strictMono.inter (measurableSet_box t)
  let D : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun σ => (fun x => x ∘ σ) ⁻¹' Dl
  have hDσ : ∀ σ, MeasurableSet (D σ) := fun σ => (perm_mp σ).measurable hDm
  have hint : ∀ σ, ∫⁻ x in D σ, f x = ∫⁻ x in Dl, f x := by
    intro σ
    have := (perm_mp σ).setLIntegral_comp_preimage hDm hf
    rw [← this]
    refine setLIntegral_congr_fun (hDσ σ) (fun x _ => ?_)
    exact (hsym σ x).symm
  have hdisj : Pairwise (Function.onFun Disjoint D) := by
    intro σ τ hστ
    rw [Function.onFun, Set.disjoint_left]
    intro x h1 h2
    apply hστ
    simp only [D, Dl, Set.mem_preimage, Set.mem_setOf_eq] at h1 h2
    have hinj : Function.Injective x := by
      intro a b hab
      have := h1.1.injective (a₁ := σ.symm a) (a₂ := σ.symm b) (by simp [hab])
      simpa using this
    have hr : Set.range (x ∘ σ) = Set.range (x ∘ τ) := by
      rw [Set.range_comp, Set.range_comp, σ.range_eq_univ, τ.range_eq_univ]
    have := (StrictMono.range_inj h1.1 h2.1).1 hr
    ext a
    have := congrFun this a
    simp only [Function.comp_apply] at this
    rw [hinj this]
  have hcover : (⋃ σ, D σ) =ᵐ[volume] B := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [injective_ae n] with x hinj
    simp only [Set.mem_iUnion, D, Dl, Set.mem_preimage, Set.mem_setOf_eq, B]
    constructor
    · rintro ⟨σ, -, h⟩ i
      have := h (σ.symm i)
      simpa using this
    · intro h
      refine ⟨Tuple.sort x, ?_, fun i => h _⟩
      exact (Tuple.monotone_sort x).strictMono_of_injective (hinj.comp (Equiv.injective _))
  rw [← setLIntegral_congr hcover, lintegral_iUnion hDσ hdisj, tsum_fintype]
  simp_rw [hint]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-! ### The count probability under a product measure -/

noncomputable def Fq (ν : Measure ℝ) {n : ℕ} (t : ℝ) (x : ℕ) (s : Fin n → ℝ) : ENNReal :=
  ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard x,
    ∏ i, (if i ∈ A then ν (Set.Ioi (t - s i)) else ν (Set.Iic (t - s i)))

lemma pi_count_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] {n : ℕ} (t : ℝ) (x : ℕ)
    (s : Fin n → ℝ) :
    Measure.pi (fun _ : Fin n => ν)
      {l | (Finset.univ.filter (fun i => t < s i + l i)).card = x} = Fq ν t x s := by
  classical
  have hset : {l : Fin n → ℝ | (Finset.univ.filter (fun i => t < s i + l i)).card = x} =
      ⋃ A ∈ (Finset.univ : Finset (Fin n)).powersetCard x,
        Set.univ.pi (fun i => if i ∈ A then Set.Ioi (t - s i) else Set.Iic (t - s i)) := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, Set.mem_univ_pi, exists_prop]
    constructor
    · intro h
      refine ⟨_, h, fun i => ?_⟩
      split_ifs with hi
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Set.mem_Ioi]; linarith
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
        simp only [Set.mem_Iic]; linarith
    · rintro ⟨A, hA, h⟩
      have : Finset.univ.filter (fun i => t < s i + l i) = A := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := h i
        split_ifs at this with hi
        · simp only [Set.mem_Ioi] at this
          exact ⟨fun _ => hi, fun _ => by linarith⟩
        · simp only [Set.mem_Iic] at this
          exact ⟨fun h' => by linarith, fun h' => absurd h' hi⟩
      rw [this, hA]
  rw [hset, measure_biUnion_finset]
  · unfold Fq
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [Measure.pi_pi]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    split_ifs <;> rfl
  · intro A _ B _ hAB
    rw [Function.onFun, Set.disjoint_left]
    intro l h1 h2
    apply hAB
    rw [Set.mem_univ_pi] at h1 h2
    ext i
    have a1 := h1 i
    have a2 := h2 i
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
      simp only [hA, hB, if_true, if_false, Set.mem_Ioi, Set.mem_Iic] at a1 a2 <;>
      simp only [hA, hB] <;> linarith
  · intro A _
    exact MeasurableSet.univ_pi (fun i => by split_ifs; exacts [measurableSet_Ioi, measurableSet_Iic])

lemma Fq_perm (ν : Measure ℝ) {n : ℕ} (t : ℝ) (x : ℕ) (σ : Equiv.Perm (Fin n))
    (s : Fin n → ℝ) : Fq ν t x (s ∘ σ) = Fq ν t x s := by
  classical
  unfold Fq
  refine Finset.sum_nbij' (fun A => A.map σ.toEmbedding) (fun A => A.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hA ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map]; exact hA.2⟩
  · intro A hA
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hA ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map]; exact hA.2⟩
  · intro A _
    ext i; simp
  · intro A _
    ext i; simp
  · intro A _
    refine Eq.trans ?_ (Equiv.prod_comp σ _)
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have : (σ i ∈ A.map σ.toEmbedding) ↔ i ∈ A := by simp
    simp only [Function.comp_apply, this]

lemma Fq_meas (ν : Measure ℝ) {n : ℕ} (t : ℝ) (x : ℕ) : Measurable (Fq ν t x (n := n)) := by
  have hm1 : Measurable (fun u => ν (Set.Ioi (t - u))) :=
    Monotone.measurable (fun a b hab => measure_mono (Set.Ioi_subset_Ioi (by linarith)))
  have hm2 : Measurable (fun u => ν (Set.Iic (t - u))) :=
    Antitone.measurable (fun a b hab => measure_mono (Set.Iic_subset_Iic.2 (by linarith)))
  unfold Fq
  refine Finset.measurable_sum _ (fun A _ => Finset.measurable_prod _ (fun i _ => ?_))
  by_cases hi : i ∈ A
  · simp only [hi, if_true]; exact hm1.comp (measurable_pi_apply i)
  · simp only [hi, if_false]; exact hm2.comp (measurable_pi_apply i)

lemma box_integral (ν : Measure ℝ) {n : ℕ} (t : ℝ) (x : ℕ) :
    ∫⁻ s in {s : Fin n → ℝ | ∀ i, 0 < s i ∧ s i < t}, Fq ν t x s =
      (n.choose x : ENNReal) * ((∫⁻ u in Set.Ioo 0 t, ν (Set.Ioi (t - u))) ^ x *
        (∫⁻ u in Set.Ioo 0 t, ν (Set.Iic (t - u))) ^ (n - x)) := by
  classical
  have hm1 : Measurable (fun u => ν (Set.Ioi (t - u))) :=
    Monotone.measurable (fun a b hab => measure_mono (Set.Ioi_subset_Ioi (by linarith)))
  have hm2 : Measurable (fun u => ν (Set.Iic (t - u))) :=
    Antitone.measurable (fun a b hab => measure_mono (Set.Iic_subset_Iic.2 (by linarith)))
  have hB : {s : Fin n → ℝ | ∀ i, 0 < s i ∧ s i < t} = Set.univ.pi (fun _ => Set.Ioo 0 t) := by
    ext s; simp
  rw [hB, volume_pi, Measure.restrict_pi_pi]
  unfold Fq
  have hf : ∀ A : Finset (Fin n), ∀ i, Measurable
      (fun u => if i ∈ A then ν (Set.Ioi (t - u)) else ν (Set.Iic (t - u))) := by
    intro A i
    by_cases hi : i ∈ A
    · simp only [hi, if_true]; exact hm1
    · simp only [hi, if_false]; exact hm2
  have hmeasA : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard x, Measurable
      (fun s : Fin n → ℝ => ∏ i, if i ∈ A then ν (Set.Ioi (t - s i)) else ν (Set.Iic (t - s i))) :=
    fun A _ => Finset.measurable_prod _ (fun i _ => (hf A i).comp (measurable_pi_apply i))
  rw [lintegral_finset_sum _ hmeasA]
  rw [Finset.sum_congr rfl (g := fun _ => (∫⁻ u in Set.Ioo 0 t, ν (Set.Ioi (t - u))) ^ x *
      (∫⁻ u in Set.Ioo 0 t, ν (Set.Iic (t - u))) ^ (n - x))]
  · rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  · intro A hA
    rw [Finset.mem_powersetCard] at hA
    refine Eq.trans (lintegral_pi_prod (fun _ => volume.restrict (Set.Ioo 0 t))
      (fun i u => if i ∈ A then ν (Set.Ioi (t - u)) else ν (Set.Iic (t - u))) (hf A)) ?_
    have hc : ∀ i, (∫⁻ u in Set.Ioo 0 t,
        (if i ∈ A then ν (Set.Ioi (t - u)) else ν (Set.Iic (t - u)))) =
        if i ∈ A then ∫⁻ u in Set.Ioo 0 t, ν (Set.Ioi (t - u))
        else ∫⁻ u in Set.Ioo 0 t, ν (Set.Iic (t - u)) := by
      intro i; split_ifs <;> rfl
    simp only [hc]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h1 : (Finset.univ.filter (fun i => i ∈ A)).card = x := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]; exact hA.2
    have h2 : (Finset.univ.filter (fun i => ¬ i ∈ A)).card = n - x := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => i ∈ A)
      rw [h1, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [h1, h2]

lemma lint_aux {g : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (hg0 : ∀ v, 0 ≤ g v)
    (hint : IntegrableOn (fun u => g (t - u)) (Set.Ioo 0 t)) :
    ∫⁻ u in Set.Ioo 0 t, ENNReal.ofReal (g (t - u)) =
      ENNReal.ofReal (∫ u in (0:ℝ)..t, g u) := by
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun u => hg0 _)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
    intervalIntegral.integral_comp_sub_left (fun v => g v) t]
  simp

lemma lint_Ioi (ν : Measure ℝ) [IsProbabilityMeasure ν] {t : ℝ} (ht : 0 < t) :
    ∫⁻ u in Set.Ioo 0 t, ν (Set.Ioi (t - u)) =
      ENNReal.ofReal (∫ u in (0:ℝ)..t, (1 - (ν (Set.Iic u)).toReal)) := by
  have hpt : ∀ v, ν (Set.Ioi v) = ENNReal.ofReal (1 - (ν (Set.Iic v)).toReal) := by
    intro v
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [hpt]
  refine lint_aux (g := fun v => 1 - (ν (Set.Iic v)).toReal) ht (fun v => sub_nonneg.2 ?_) ?_
  · have := prob_le_one (μ := ν) (s := Set.Iic v)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  · refine (MonotoneOn.integrableOn_isCompact isCompact_Icc ?_).mono_set Set.Ioo_subset_Icc_self
    intro a _ b _ hab
    have : ν (Set.Iic (t - b)) ≤ ν (Set.Iic (t - a)) :=
      measure_mono (Set.Iic_subset_Iic.2 (by linarith))
    have := ENNReal.toReal_mono (measure_ne_top _ _) this
    simp only; linarith

lemma lint_Iic (ν : Measure ℝ) [IsProbabilityMeasure ν] {t : ℝ} (ht : 0 < t) :
    ∫⁻ u in Set.Ioo 0 t, ν (Set.Iic (t - u)) =
      ENNReal.ofReal (∫ u in (0:ℝ)..t, (ν (Set.Iic u)).toReal) := by
  have hpt : ∀ v, ν (Set.Iic v) = ENNReal.ofReal ((ν (Set.Iic v)).toReal) := by
    intro v; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  conv_lhs => enter [2, u]; rw [hpt]
  refine lint_aux (g := fun v => (ν (Set.Iic v)).toReal) ht (fun v => ENNReal.toReal_nonneg) ?_
  refine (AntitoneOn.integrableOn_isCompact isCompact_Icc ?_).mono_set Set.Ioo_subset_Icc_self
  intro a _ b _ hab
  have : ν (Set.Iic (t - b)) ≤ ν (Set.Iic (t - a)) :=
    measure_mono (Set.Iic_subset_Iic.2 (by linarith))
  exact ENNReal.toReal_mono (measure_ne_top _ _) this

/-! ### The probabilistic part -/

noncomputable def cntv (S : ResupplySystem Ω P) (t : ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => t < S.arrival i ω + S.resupply i ω)).card

lemma units_eq (S : ResupplySystem Ω P) {t : ℝ} {ω : Ω} (hω : ∀ k, 0 ≤ S.gap k ω) {n : ℕ}
    (h : psum S n ω ≤ t ∧ t < psum S (n + 1) ω) :
    S.unitsInResupply t ω = cntv S t n ω := by
  classical
  have hset : {k : ℕ | S.arrival k ω ≤ t ∧ t < S.arrival k ω + S.resupply k ω} =
      ↑((Finset.range n).filter (fun k => t < S.arrival k ω + S.resupply k ω)) := by
    ext k
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hk; push_neg at hk
      have := psum_mono S hω (show n + 1 ≤ k + 1 by omega)
      rw [arrival_eq] at h1
      linarith [h.2]
    · rintro ⟨hk, h2⟩
      refine ⟨?_, h2⟩
      have := psum_mono S hω (show k + 1 ≤ n by omega)
      rw [arrival_eq]; linarith [h.1]
  unfold ResupplySystem.unitsInResupply cntv
  rw [hset, Set.ncard_coe_finset, Finset.card_filter, Finset.card_filter]
  exact (Fin.sum_univ_eq_sum_range
    (fun k => if t < S.arrival k ω + S.resupply k ω then 1 else 0) n).symm

lemma X_eq_cnt [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t)
    (n x : ℕ) :
    ({ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n} : Set Ω) =ᵐ[P]
      ({ω | cntv S t n ω = x} ∩ {ω | psum S n ω ≤ t ∧ t < psum S (n + 1) ω} : Set Ω) := by
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [gap_nonneg_ae S, finite_ae S ht.le] with ω hω hK
  show (S.unitsInResupply t ω = x ∧ S.orderCount t ω = n) ↔
    (cntv S t n ω = x ∧ (psum S n ω ≤ t ∧ t < psum S (n + 1) ω))
  rw [count_iff S ht.le hω hK n]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(units_eq S hω h2) ▸ h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(units_eq S hω h2).symm ▸ h1, h2⟩

lemma E_eq_N [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    ({ω | psum S n ω ≤ t ∧ t < psum S (n + 1) ω} : Set Ω) =ᵐ[P] {ω | S.orderCount t ω = n} := by
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [gap_nonneg_ae S, finite_ae S ht.le] with ω hω hK
  show (psum S n ω ≤ t ∧ t < psum S (n + 1) ω) ↔ S.orderCount t ω = n
  rw [count_iff S ht.le hω hK n]

lemma joint_indep [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (n : ℕ) :
    IndepFun (fun ω => ((fun i : Fin n => S.arrival i ω), psum S n ω, psum S (n + 1) ω))
      (fun ω => fun i : Fin n => S.resupply i ω) P := by
  classical
  have hmeas : ∀ i, Measurable (Sum.elim S.gap S.resupply i) := by
    rintro (k | k)
    · exact S.gap_measurable k
    · exact S.resupply_measurable k
  let A : Finset (ℕ ⊕ ℕ) := (Finset.range (n + 1)).map (Function.Embedding.inl (β := ℕ))
  let B : Finset (ℕ ⊕ ℕ) := (Finset.range n).map (Function.Embedding.inr (α := ℕ))
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [A, B, Finset.mem_map, Finset.mem_range, Function.Embedding.inl_apply,
      Function.Embedding.inr_apply] at ha hb
    obtain ⟨k, -, rfl⟩ := ha
    obtain ⟨j, -, hj⟩ := hb
    cases hj
  have h := S.indep.indepFun_finset _ _ hd hmeas
  let get : (A → ℝ) → ℕ → ℝ := fun v k => if hk : Sum.inl k ∈ A then v ⟨Sum.inl k, hk⟩ else 0
  have hget : ∀ k, Measurable (fun v : A → ℝ => get v k) := by
    intro k
    by_cases hk : Sum.inl k ∈ A
    · simp only [get, hk, dif_pos]; exact measurable_pi_apply _
    · simp only [get, hk, dif_neg, not_false_eq_true]; exact measurable_const
  let φ : (A → ℝ) → (Fin n → ℝ) × ℝ × ℝ := fun v =>
    ((fun i : Fin n => ∑ k ∈ Finset.range (i.val + 1), get v k),
      ∑ k ∈ Finset.range n, get v k, ∑ k ∈ Finset.range (n + 1), get v k)
  have hφ : Measurable φ := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact measurable_pi_lambda _ (fun i => Finset.measurable_sum _ (fun k _ => hget k))
    · exact Finset.measurable_sum _ (fun k _ => hget k)
    · exact Finset.measurable_sum _ (fun k _ => hget k)
  have hmemB : ∀ i : Fin n, (Sum.inr i.val : ℕ ⊕ ℕ) ∈ B := by
    intro i; simp [B]
  have hψ : Measurable (fun v : B → ℝ => fun i : Fin n => v ⟨Sum.inr i.val, hmemB i⟩) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have h2 := h.comp hφ hψ
  have hg : ∀ ω, ∀ k, k < n + 1 →
      get (fun i : A => Sum.elim S.gap S.resupply i ω) k = S.gap k ω := by
    intro ω k hk
    have hm : Sum.inl k ∈ A := by simp [A]; omega
    simp only [get, dif_pos hm]; rfl
  convert h2 using 1
  · funext ω
    simp only [Function.comp_apply, φ]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      simp only [ResupplySystem.arrival]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_range] at hk
      rw [hg ω k (by omega)]
    · simp only [psum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_range] at hk
      rw [hg ω k (by omega)]
    · simp only [psum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_range] at hk
      rw [hg ω k (by omega)]
  · rfl

lemma Lv_law [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (n : ℕ) :
    P.map (fun ω => fun i : Fin n => S.resupply i ω) =
      Measure.pi (fun _ => volume.withDensity S.density) := by
  have hi : iIndepFun (fun (i : Fin n) ω => S.resupply i.val ω) P :=
    S.indep.precomp (g := fun i : Fin n => (Sum.inr i.val : ℕ ⊕ ℕ))
      (by intro a b hab; simp only [Sum.inr.injEq] at hab; exact Fin.ext hab)
  refine ((iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin n) ω => S.resupply i.val ω)
    (fun i => (S.resupply_measurable i.val).aemeasurable)).1 hi).trans ?_
  congr 1; funext i; exact S.resupply_law i.val

lemma nu_prob [IsProbabilityMeasure P] (S : ResupplySystem Ω P) :
    IsProbabilityMeasure (volume.withDensity S.density) := by
  rw [← S.resupply_law 0]
  exact Measure.isProbabilityMeasure_map (S.resupply_measurable 0).aemeasurable

lemma cdf_eq (S : ResupplySystem Ω P) (u : ℝ) :
    S.resupplyCdf u = ((volume.withDensity S.density) (Set.Iic u)).toReal := by
  rw [← S.resupply_law 0, Measure.map_apply (S.resupply_measurable 0) measurableSet_Iic]
  rfl

lemma Tv_meas (S : ResupplySystem Ω P) (n : ℕ) :
    Measurable (fun ω => fun i : Fin n => S.arrival i ω) :=
  measurable_pi_lambda _ (fun i => psum_meas S (i.val + 1))

theorem binom_enn [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t)
    (n x : ℕ) :
    P ({ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n}) =
      (P {ω | S.orderCount t ω = n} * ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n)) *
        ((Nat.factorial n : ENNReal)⁻¹ * ((n.choose x : ENNReal) *
          (ENNReal.ofReal (∫ u in (0:ℝ)..t, (1 - S.resupplyCdf u)) ^ x *
           ENNReal.ofReal (∫ u in (0:ℝ)..t, S.resupplyCdf u) ^ (n - x)))) := by
  classical
  set ν := volume.withDensity S.density with hν
  haveI := nu_prob S
  set Tv := fun ω => fun i : Fin n => S.arrival i ω with hTv
  set Lv := fun ω => fun i : Fin n => S.resupply i ω with hLv
  set Z := fun ω => ((fun i : Fin n => S.arrival i ω), psum S n ω, psum S (n + 1) ω) with hZ
  have hTm : Measurable Tv := Tv_meas S n
  have hZm : Measurable Z := hTm.prodMk ((psum_meas S n).prodMk (psum_meas S (n + 1)))
  have hLm : Measurable Lv := measurable_pi_lambda _ (fun i => S.resupply_measurable i.val)
  set E := {ω | psum S n ω ≤ t ∧ t < psum S (n + 1) ω} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_le (psum_meas S n) measurable_const).inter
      (measurableSet_lt measurable_const (psum_meas S (n + 1)))
  -- step 1
  rw [measure_congr (X_eq_cnt S ht n x)]
  -- step 2
  set Q := {p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → ℝ) |
    (Finset.univ.filter (fun i => t < p.1.1 i + p.2 i)).card = x ∧ p.1.2.1 ≤ t ∧ t < p.1.2.2}
    with hQ
  have hcardR : Measurable (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → ℝ) =>
      ((Finset.univ.filter (fun i => t < p.1.1 i + p.2 i)).card : ℝ)) := by
    simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    refine Finset.measurable_sum _ (fun i _ => Measurable.ite ?_ measurable_const measurable_const)
    exact measurableSet_lt measurable_const
      (((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).add
        ((measurable_pi_apply i).comp measurable_snd))
  have hQm : MeasurableSet Q := by
    have : Q = {p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → ℝ) |
        ((Finset.univ.filter (fun i => t < p.1.1 i + p.2 i)).card : ℝ) = (x : ℝ)} ∩
        ({p | p.1.2.1 ≤ t} ∩ {p | t < p.1.2.2}) := by
      ext p; simp only [hQ, Set.mem_setOf_eq, Set.mem_inter_iff, Nat.cast_inj]
    rw [this]
    refine (measurableSet_eq_fun hcardR measurable_const).inter
      ((measurableSet_le ?_ measurable_const).inter (measurableSet_lt measurable_const ?_))
    · exact measurable_fst.comp (measurable_snd.comp measurable_fst)
    · exact measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hpre : {ω | cntv S t n ω = x} ∩ E = (fun ω => (Z ω, Lv ω)) ⁻¹' Q := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, hQ, hE, cntv, Z, Lv]
  have hslice : ∀ z : (Fin n → ℝ) × ℝ × ℝ, (P.map Lv) (Prod.mk z ⁻¹' Q) =
      Set.indicator {z : (Fin n → ℝ) × ℝ × ℝ | z.2.1 ≤ t ∧ t < z.2.2}
        (fun z => Fq ν t x z.1) z := by
    intro z
    rw [Lv_law S n]
    by_cases hz : z.2.1 ≤ t ∧ t < z.2.2
    · rw [Set.indicator_of_mem (by exact hz), ← pi_count_eq ν t x z.1]
      congr 1
      ext l; simp only [Set.mem_preimage, hQ, Set.mem_setOf_eq, hz, and_true]
    · rw [Set.indicator_of_notMem (by exact hz)]
      have : Prod.mk z ⁻¹' Q = ∅ := by
        ext l; simp only [Set.mem_preimage, hQ, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro _ h1 h2; exact hz ⟨h1, h2⟩
      rw [this, measure_empty]
  have hEz : MeasurableSet {z : (Fin n → ℝ) × ℝ × ℝ | z.2.1 ≤ t ∧ t < z.2.2} :=
    (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))
  have hFm := Fq_meas ν t x (n := n)
  have step2 : P ({ω | cntv S t n ω = x} ∩ E) = ∫⁻ ω in E, Fq ν t x (Tv ω) ∂P := by
    rw [hpre, ← Measure.map_apply (hZm.prodMk hLm) hQm,
      (indepFun_iff_map_prod_eq_prod_map_map hZm.aemeasurable hLm.aemeasurable).1
        (joint_indep S n), Measure.prod_apply hQm]
    simp_rw [hslice]
    rw [lintegral_map (f := {z : (Fin n → ℝ) × ℝ × ℝ | z.2.1 ≤ t ∧ t < z.2.2}.indicator
        (fun z => Fq ν t x z.1)) ((hFm.comp measurable_fst).indicator hEz) hZm,
      ← lintegral_indicator hEm]
    rfl
  rw [step2, setLIntegral_congr (E_eq_N S ht n)]
  -- step 3 : order statistics
  have hmeasure : (P.restrict {ω | S.orderCount t ω = n}).map Tv =
      (P {ω | S.orderCount t ω = n} * ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n)) •
        volume.restrict {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t} := by
    ext A hA
    rw [Measure.map_apply hTm hA, Measure.restrict_apply (hTm hA), Measure.smul_apply,
      Measure.restrict_apply hA, smul_eq_mul, Set.inter_comm]
    exact (arrival_os_core S ht n hA).trans (mul_assoc _ _ _).symm
  rw [← lintegral_map hFm hTm, hmeasure, lintegral_smul_measure]
  congr 1
  -- step 4 : symmetrization
  have hs := sym_lintegral t (Fq ν t x) hFm (fun σ s => Fq_perm ν t x σ s)
  have hne : (Nat.factorial n : ENNReal) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [box_integral, lint_Ioi ν ht, lint_Iic ν ht] at hs
  rw [hν] at hs
  simp_rw [← cdf_eq S] at hs
  rw [hs, ← mul_assoc, ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _), one_mul]

/-! ### Real-valued forms -/

lemma cdf_bounds [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (u : ℝ) :
    0 ≤ S.resupplyCdf u ∧ S.resupplyCdf u ≤ 1 := by
  unfold ResupplySystem.resupplyCdf
  refine ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one ?_⟩
  rw [ENNReal.ofReal_one]; exact prob_le_one

lemma cdf_mono [IsProbabilityMeasure P] (S : ResupplySystem Ω P) : Monotone S.resupplyCdf := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (fun ω (h : S.resupply 0 ω ≤ a) => show S.resupply 0 ω ≤ b from h.trans hab))

theorem binom_real [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t)
    (n x : ℕ) :
    (P ({ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n})).toReal =
      (P {ω | S.orderCount t ω = n}).toReal *
        ((Nat.choose n x : ℝ) * ((1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x *
          (1 - (1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ (n - x)) := by
  rw [binom_enn S ht n x]
  set I := ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u) with hI
  set J := ∫ u in (0 : ℝ)..t, S.resupplyCdf u with hJ
  have hJint : IntervalIntegrable S.resupplyCdf volume 0 t := (cdf_mono S).intervalIntegrable
  have hIJ : I = t - J := by
    rw [hI, intervalIntegral.integral_sub intervalIntegrable_const hJint, ← hJ]
    simp
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht.le
    (fun u _ => sub_nonneg.2 (cdf_bounds S u).2)
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg ht.le (fun u _ => (cdf_bounds S u).1)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg _)
    (pow_nonneg ht.le _)), ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hI0, ENNReal.toReal_ofReal hJ0]
  rcases le_or_gt x n with hxn | hxn
  · have h1 : 1 - (1 / t) * I = J / t := by rw [hIJ]; field_simp; ring
    rw [h1]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hxn
    rw [Nat.add_sub_cancel_left]
    have hf : ((x + m).factorial : ℝ) ≠ 0 := by positivity
    have htn : t ≠ 0 := ht.ne'
    rw [div_pow, mul_pow, pow_add]
    simp only [one_div, inv_pow]
    field_simp
    try ring
  · rw [Nat.choose_eq_zero_of_lt hxn]; simp

lemma cntv_meas (S : ResupplySystem Ω P) (t : ℝ) (n : ℕ) :
    Measurable (fun ω => (cntv S t n ω : ℝ)) := by
  unfold cntv
  simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  refine Finset.measurable_sum _ (fun i _ => Measurable.ite ?_ measurable_const measurable_const)
  exact measurableSet_lt measurable_const ((psum_meas S _).add (S.resupply_measurable _))

theorem poisson_core [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t)
    (x : ℕ) :
    (P {ω | S.unitsInResupply t ω = x}).toReal =
      Real.exp (-(S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u))) *
        (S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x / (Nat.factorial x : ℝ) := by
  set I := ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u) with hI
  set f : ℕ → Set Ω := fun n => {ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n}
    with hf
  have hU : {ω | S.unitsInResupply t ω = x} = ⋃ n, f n := by
    ext ω
    simp only [hf, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨_, h, _⟩; exact h
  have hdisj : Pairwise (Function.onFun (AEDisjoint P) f) := by
    intro a b hab
    refine Disjoint.aedisjoint ?_
    rw [Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    exact hab (h1.symm.trans h2)
  have hnm : ∀ n, NullMeasurableSet (f n) P := by
    intro n
    refine NullMeasurableSet.congr ?_ (X_eq_cnt S ht n x).symm
    refine MeasurableSet.nullMeasurableSet ?_
    have : {ω | cntv S t n ω = x} = {ω | (cntv S t n ω : ℝ) = (x : ℝ)} := by
      ext ω; simp only [Set.mem_setOf_eq, Nat.cast_inj]
    rw [this]
    exact (measurableSet_eq_fun (cntv_meas S t n) measurable_const).inter
      ((measurableSet_le (psum_meas S n) measurable_const).inter
        (measurableSet_lt measurable_const (psum_meas S (n + 1))))
  rw [hU, measure_iUnion₀ hdisj hnm, ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)]
  simp only [hf, binom_real S ht, order_count_core S ht]
  -- the Poisson thinning sum
  set a := S.rate * t with ha
  set p := (1 / t) * I with hp
  have hap : S.rate * I = a * p := by rw [ha, hp]; field_simp
  rw [hap]
  refine HasSum.tsum_eq ?_
  have hzero : ∑ i ∈ Finset.range x, Real.exp (-a) * a ^ i / (Nat.factorial i : ℝ) *
      ((Nat.choose i x : ℝ) * p ^ x * (1 - p) ^ (i - x)) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [Nat.choose_eq_zero_of_lt hi]; simp
  have hexp := (NormedSpace.expSeries_div_hasSum_exp (a * (1 - p))).mul_left
    (Real.exp (-a) * (a * p) ^ x / (Nat.factorial x : ℝ))
  rw [← Real.exp_eq_exp_ℝ] at hexp
  have hval : Real.exp (-(a * p)) * (a * p) ^ x / (Nat.factorial x : ℝ) =
      Real.exp (-a) * (a * p) ^ x / (Nat.factorial x : ℝ) * Real.exp (a * (1 - p)) := by
    rw [show -(a * p) = -a + a * (1 - p) by ring, Real.exp_add]; ring
  have hfun : (fun m : ℕ => Real.exp (-a) * a ^ (m + x) / ((m + x).factorial : ℝ) *
      (((m + x).choose x : ℝ) * p ^ x * (1 - p) ^ (m + x - x))) =
      fun m => Real.exp (-a) * (a * p) ^ x / (Nat.factorial x : ℝ) *
        ((a * (1 - p)) ^ m / (m.factorial : ℝ)) := by
    funext m
    rw [Nat.add_sub_cancel]
    have hc := Nat.add_choose_mul_factorial_mul_factorial m x
    have hc' : ((m + x).factorial : ℝ) =
        ((m + x).choose x : ℝ) * (m.factorial : ℝ) * (x.factorial : ℝ) := by
      exact_mod_cast hc.symm
    have h1 : ((m + x).choose x : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_left x m)).ne'
    have h2 : (m.factorial : ℝ) ≠ 0 := by positivity
    have h3 : (x.factorial : ℝ) ≠ 0 := by positivity
    rw [hc', mul_pow a (1 - p) m, mul_pow a p x]
    field_simp
    try ring
  rw [hval]
  refine (hasSum_nat_add_iff' x).1 ?_
  rw [hzero, sub_zero]
  exact hfun ▸ hexp
end ServiceParts.Palm

open ServiceParts.Palm


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (x : ℕ) :
    (P {ω | S.unitsInResupply t ω = x}).toReal =
      Real.exp (-(S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u))) *
        (S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x / (Nat.factorial x : ℝ) := by
  exact poisson_core S ht x
