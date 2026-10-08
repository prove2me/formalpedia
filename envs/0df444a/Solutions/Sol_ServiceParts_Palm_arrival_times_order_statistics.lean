-- Prove2me | solution 1 for ServiceParts.Palm.arrival_times_order_statistics
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T10:31:41.60501+00:00
-- url     : https://prove2.me/submissions/417cdff8-2f1a-46c2-aaa8-5637746e371d

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

end ServiceParts.Palm

open ServiceParts.Palm


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (n : ℕ)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    P ({ω | S.orderCount t ω = n} ∩ {ω | (fun i : Fin n => S.arrival i ω) ∈ A}) =
      P {ω | S.orderCount t ω = n} *
        (ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n) *
          volume (A ∩ {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t})) := by
  exact arrival_os_core S ht n hA
