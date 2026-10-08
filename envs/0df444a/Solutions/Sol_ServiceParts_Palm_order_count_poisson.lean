-- Prove2me | solution 1 for ServiceParts.Palm.order_count_poisson
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T10:22:01.302502+00:00
-- url     : https://prove2.me/submissions/b461a323-bc3f-42ec-8594-f6d115d8d7b6

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

end ServiceParts.Palm

open ServiceParts.Palm


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (P {ω | S.orderCount t ω = n}).toReal =
      Real.exp (-(S.rate * t)) * (S.rate * t) ^ n / (Nat.factorial n : ℝ) := by
  exact order_count_core S ht n
