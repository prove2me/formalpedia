-- Prove2me | solution 1 for ServiceParts.Palm.compound_palm_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:35:47.40175+00:00
-- url     : https://prove2.me/submissions/d393c1b1-d31b-4cc9-b4b5-380bf36088bf

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem
import Definitions.Def_ServiceParts_Palm_CompoundResupplySystem

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

/-! ### General version of the count probability -/

noncomputable def Fg (ν : Measure ℝ) {n : ℕ} (B : ℝ → Set ℝ) (x : ℕ) (s : Fin n → ℝ) : ENNReal :=
  ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard x,
    ∏ i, (if i ∈ A then ν (B (s i)) else ν (B (s i))ᶜ)

open Classical in
lemma pi_count_g (ν : Measure ℝ) [IsProbabilityMeasure ν] {n : ℕ} (B : ℝ → Set ℝ)
    (hB : ∀ u, MeasurableSet (B u)) (x : ℕ) (s : Fin n → ℝ) :
    Measure.pi (fun _ : Fin n => ν)
      {l | (Finset.univ.filter (fun i => l i ∈ B (s i))).card = x} = Fg ν B x s := by
  classical
  have hset : {l : Fin n → ℝ | (Finset.univ.filter (fun i => l i ∈ B (s i))).card = x} =
      ⋃ A ∈ (Finset.univ : Finset (Fin n)).powersetCard x,
        Set.univ.pi (fun i => if i ∈ A then B (s i) else (B (s i))ᶜ) := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, Set.mem_univ_pi, exists_prop]
    constructor
    · intro h
      refine ⟨_, h, fun i => ?_⟩
      split_ifs with hi
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hi
    · rintro ⟨A, hA, h⟩
      have : Finset.univ.filter (fun i => l i ∈ B (s i)) = A := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := h i
        split_ifs at this with hi
        · exact ⟨fun _ => hi, fun _ => this⟩
        · exact ⟨fun h' => absurd h' this, fun h' => absurd h' hi⟩
      rw [this, hA]
  rw [hset, measure_biUnion_finset]
  · unfold Fg
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [Measure.pi_pi]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    split_ifs <;> rfl
  · intro A _ C _ hAC
    rw [Function.onFun, Set.disjoint_left]
    intro l h1 h2
    apply hAC
    rw [Set.mem_univ_pi] at h1 h2
    ext i
    have a1 := h1 i
    have a2 := h2 i
    by_cases hA : i ∈ A <;> by_cases hC : i ∈ C <;>
      simp only [hA, hC, if_true, if_false, Set.mem_compl_iff] at a1 a2 <;>
      simp only [hA, hC]
    · exact (a2 a1).elim
    · exact (a1 a2).elim
  · intro A _
    exact MeasurableSet.univ_pi (fun i => by
      split_ifs
      exacts [hB _, (hB _).compl])

lemma Fg_perm (ν : Measure ℝ) {n : ℕ} (B : ℝ → Set ℝ) (x : ℕ) (σ : Equiv.Perm (Fin n))
    (s : Fin n → ℝ) : Fg ν B x (s ∘ σ) = Fg ν B x s := by
  classical
  unfold Fg
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

lemma Fg_meas (ν : Measure ℝ) {n : ℕ} (B : ℝ → Set ℝ) (x : ℕ)
    (hm1 : Measurable (fun u => ν (B u))) (hm2 : Measurable (fun u => ν (B u)ᶜ)) :
    Measurable (Fg ν B x (n := n)) := by
  unfold Fg
  refine Finset.measurable_sum _ (fun A _ => Finset.measurable_prod _ (fun i _ => ?_))
  by_cases hi : i ∈ A
  · simp only [hi, if_true]; exact hm1.comp (measurable_pi_apply i)
  · simp only [hi, if_false]; exact hm2.comp (measurable_pi_apply i)

lemma box_integral_g (ν : Measure ℝ) {n : ℕ} (B : ℝ → Set ℝ) (t : ℝ) (x : ℕ)
    (hm1 : Measurable (fun u => ν (B u))) (hm2 : Measurable (fun u => ν (B u)ᶜ)) :
    ∫⁻ s in {s : Fin n → ℝ | ∀ i, 0 < s i ∧ s i < t}, Fg ν B x s =
      (n.choose x : ENNReal) * ((∫⁻ u in Set.Ioo 0 t, ν (B u)) ^ x *
        (∫⁻ u in Set.Ioo 0 t, ν (B u)ᶜ) ^ (n - x)) := by
  classical
  have hB : {s : Fin n → ℝ | ∀ i, 0 < s i ∧ s i < t} = Set.univ.pi (fun _ => Set.Ioo 0 t) := by
    ext s; simp
  rw [hB, volume_pi, Measure.restrict_pi_pi]
  unfold Fg
  have hf : ∀ A : Finset (Fin n), ∀ i, Measurable
      (fun u => if i ∈ A then ν (B u) else ν (B u)ᶜ) := by
    intro A i
    by_cases hi : i ∈ A
    · simp only [hi, if_true]; exact hm1
    · simp only [hi, if_false]; exact hm2
  have hmeasA : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard x, Measurable
      (fun s : Fin n → ℝ => ∏ i, if i ∈ A then ν (B (s i)) else ν (B (s i))ᶜ) :=
    fun A _ => Finset.measurable_prod _ (fun i _ => (hf A i).comp (measurable_pi_apply i))
  rw [lintegral_finset_sum _ hmeasA]
  rw [Finset.sum_congr rfl (g := fun _ => (∫⁻ u in Set.Ioo 0 t, ν (B u)) ^ x *
      (∫⁻ u in Set.Ioo 0 t, ν (B u)ᶜ) ^ (n - x))]
  · rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  · intro A hA
    rw [Finset.mem_powersetCard] at hA
    refine Eq.trans (lintegral_pi_prod (fun _ => volume.restrict (Set.Ioo 0 t))
      (fun i u => if i ∈ A then ν (B u) else ν (B u)ᶜ) (hf A)) ?_
    have hc : ∀ i, (∫⁻ u in Set.Ioo 0 t, (if i ∈ A then ν (B u) else ν (B u)ᶜ)) =
        if i ∈ A then ∫⁻ u in Set.Ioo 0 t, ν (B u) else ∫⁻ u in Set.Ioo 0 t, ν (B u)ᶜ := by
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

/-- the aged acceptance set: order placed at `u` is counted iff `u + T ≤ t < u + l` -/
def Bset (T t : ℝ) (u : ℝ) : Set ℝ := {l | u + T ≤ t ∧ t < u + l}

lemma Bset_meas (T t u : ℝ) : MeasurableSet (Bset T t u) := by
  by_cases h : u + T ≤ t
  · have : Bset T t u = {l | t < u + l} := by ext l; simp [Bset, h]
    rw [this]; exact measurableSet_lt measurable_const (measurable_const.add measurable_id)
  · have : Bset T t u = ∅ := by ext l; simp [Bset, h]
    rw [this]; exact MeasurableSet.empty

/-- the real density of `ν (Bset T t u)` -/
noncomputable def hB (ν : Measure ℝ) (T t : ℝ) (u : ℝ) : ℝ :=
  if u + T ≤ t then 1 - (ν (Set.Iic (t - u))).toReal else 0

lemma nuB_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (T t u : ℝ) :
    ν (Bset T t u) = ENNReal.ofReal (hB ν T t u) := by
  unfold hB
  by_cases h : u + T ≤ t
  · have : Bset T t u = Set.Ioi (t - u) := by
      ext l; simp only [Bset, h, true_and, Set.mem_setOf_eq, Set.mem_Ioi]
      constructor <;> intro <;> linarith
    rw [this, if_pos h, ← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
      ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_one,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · have : Bset T t u = ∅ := by ext l; simp [Bset, h]
    rw [this, if_neg h]; simp

lemma nuBc_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] (T t u : ℝ) :
    ν (Bset T t u)ᶜ = ENNReal.ofReal (1 - hB ν T t u) := by
  have h0 : 0 ≤ hB ν T t u := by
    unfold hB; split_ifs
    · have := prob_le_one (μ := ν) (s := Set.Iic (t - u))
      have := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
      linarith
    · exact le_rfl
  rw [prob_compl_eq_one_sub (Bset_meas T t u), nuB_eq, ← ENNReal.ofReal_one,
    ENNReal.ofReal_sub _ h0]

lemma hB_meas (ν : Measure ℝ) (T t : ℝ) : Measurable (hB ν T t) := by
  unfold hB
  refine Measurable.ite (measurableSet_le (measurable_id.add measurable_const) measurable_const)
    ?_ measurable_const
  refine measurable_const.sub (Antitone.measurable (fun a b hab => ?_)).ennreal_toReal
  exact measure_mono (Set.Iic_subset_Iic.2 (by linarith))

lemma hB_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] (T t u : ℝ) :
    0 ≤ hB ν T t u ∧ hB ν T t u ≤ 1 := by
  unfold hB; split_ifs
  · have := prob_le_one (μ := ν) (s := Set.Iic (t - u))
    have := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    constructor
    · linarith
    · linarith [ENNReal.toReal_nonneg (a := ν (Set.Iic (t - u)))]
  · exact ⟨le_rfl, zero_le_one⟩

lemma hB_integrable (ν : Measure ℝ) [IsProbabilityMeasure ν] (T t : ℝ) :
    IntegrableOn (hB ν T t) (Set.Ioo 0 t) := by
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioo_lt_top.ne
    (hB_meas ν T t).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hB_bounds ν T t u).1]
  exact (hB_bounds ν T t u).2

lemma lint_B (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ u in Set.Ioo 0 t, ν (Bset T t u) =
      ENNReal.ofReal (∫ u in (0:ℝ)..t, hB ν T t u) := by
  simp_rw [nuB_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal (hB_integrable ν T t)
    (Eventually.of_forall (fun u => (hB_bounds ν T t u).1)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le]

lemma lint_Bc (ν : Measure ℝ) [IsProbabilityMeasure ν] (T : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫⁻ u in Set.Ioo 0 t, ν (Bset T t u)ᶜ =
      ENNReal.ofReal (t - ∫ u in (0:ℝ)..t, hB ν T t u) := by
  simp_rw [nuBc_eq]
  have hint : IntegrableOn (fun u => 1 - hB ν T t u) (Set.Ioo 0 t) :=
    (integrableOn_const measure_Ioo_lt_top.ne).sub (hB_integrable ν T t)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall (fun u => sub_nonneg.2 (hB_bounds ν T t u).2)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
    intervalIntegral.integral_sub intervalIntegrable_const]
  · simp
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]; exact hB_integrable ν T t

/-! ### Aged binomial law on `{N(t) = m}` -/

open Classical in
noncomputable def agedCnt (S : ResupplySystem Ω P) (T t : ℝ) (m : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => S.resupply i ω ∈ Bset T t (S.arrival i ω))).card

lemma agedCnt_meas (S : ResupplySystem Ω P) (T t : ℝ) (m : ℕ) :
    Measurable (fun ω => (agedCnt S T t m ω : ℝ)) := by
  classical
  unfold agedCnt
  simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  refine Finset.measurable_sum _ (fun i _ => Measurable.ite ?_ measurable_const measurable_const)
  have : {ω | S.resupply i ω ∈ Bset T t (S.arrival i ω)} =
      {ω | S.arrival i ω + T ≤ t} ∩ {ω | t < S.arrival i ω + S.resupply i ω} := by
    ext ω; simp [Bset]
  rw [this]
  exact (measurableSet_le ((psum_meas S _).add measurable_const) measurable_const).inter
    (measurableSet_lt measurable_const ((psum_meas S _).add (S.resupply_measurable _)))

theorem aged_binom_enn [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (T : ℝ) {t : ℝ}
    (ht : 0 < t) (m y : ℕ) :
    P ({ω | agedCnt S T t m ω = y} ∩ {ω | S.orderCount t ω = m}) =
      (P {ω | S.orderCount t ω = m} * ENNReal.ofReal ((Nat.factorial m : ℝ) / t ^ m)) *
        ((Nat.factorial m : ENNReal)⁻¹ * ((m.choose y : ENNReal) *
          (ENNReal.ofReal (∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u) ^ y *
           ENNReal.ofReal (t - ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u)
             ^ (m - y)))) := by
  classical
  set ν := volume.withDensity S.density with hν
  haveI := nu_prob S
  set Tv := fun ω => fun i : Fin m => S.arrival i ω with hTv
  set Lv := fun ω => fun i : Fin m => S.resupply i ω with hLv
  set Z := fun ω => ((fun i : Fin m => S.arrival i ω), psum S m ω, psum S (m + 1) ω) with hZ
  have hTm : Measurable Tv := Tv_meas S m
  have hZm : Measurable Z := hTm.prodMk ((psum_meas S m).prodMk (psum_meas S (m + 1)))
  have hLm : Measurable Lv := measurable_pi_lambda _ (fun i => S.resupply_measurable i.val)
  set E := {ω | psum S m ω ≤ t ∧ t < psum S (m + 1) ω} with hE
  have hEm : MeasurableSet E :=
    (measurableSet_le (psum_meas S m) measurable_const).inter
      (measurableSet_lt measurable_const (psum_meas S (m + 1)))
  have hBm : ∀ u, MeasurableSet (Bset T t u) := Bset_meas T t
  have hm1 : Measurable (fun u => ν (Bset T t u)) := by
    simp_rw [nuB_eq]; exact (hB_meas ν T t).ennreal_ofReal
  have hm2 : Measurable (fun u => ν (Bset T t u)ᶜ) := by
    simp_rw [nuBc_eq]; exact (measurable_const.sub (hB_meas ν T t)).ennreal_ofReal
  -- step 1
  rw [measure_congr ((ae_eq_refl {ω | agedCnt S T t m ω = y}).inter (E_eq_N S ht m).symm)]
  -- step 2
  set Q := {p : ((Fin m → ℝ) × ℝ × ℝ) × (Fin m → ℝ) |
    (Finset.univ.filter (fun i => p.2 i ∈ Bset T t (p.1.1 i))).card = y ∧
      p.1.2.1 ≤ t ∧ t < p.1.2.2} with hQ
  have hcardR : Measurable (fun p : ((Fin m → ℝ) × ℝ × ℝ) × (Fin m → ℝ) =>
      ((Finset.univ.filter (fun i => p.2 i ∈ Bset T t (p.1.1 i))).card : ℝ)) := by
    simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    refine Finset.measurable_sum _ (fun i _ => Measurable.ite ?_ measurable_const measurable_const)
    have hfi : Measurable (fun p : ((Fin m → ℝ) × ℝ × ℝ) × (Fin m → ℝ) => p.1.1 i) :=
      (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
    have hli : Measurable (fun p : ((Fin m → ℝ) × ℝ × ℝ) × (Fin m → ℝ) => p.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    have : {p : ((Fin m → ℝ) × ℝ × ℝ) × (Fin m → ℝ) | p.2 i ∈ Bset T t (p.1.1 i)} =
        {p | p.1.1 i + T ≤ t} ∩ {p | t < p.1.1 i + p.2 i} := by
      ext p; simp [Bset]
    rw [this]
    exact (measurableSet_le (hfi.add measurable_const) measurable_const).inter
      (measurableSet_lt measurable_const (hfi.add hli))
  have hQm : MeasurableSet Q := by
    have : Q = {p : ((Fin m → ℝ) × ℝ × ℝ) × (Fin m → ℝ) |
        ((Finset.univ.filter (fun i => p.2 i ∈ Bset T t (p.1.1 i))).card : ℝ) = (y : ℝ)} ∩
        ({p | p.1.2.1 ≤ t} ∩ {p | t < p.1.2.2}) := by
      ext p; simp only [hQ, Set.mem_setOf_eq, Set.mem_inter_iff, Nat.cast_inj]
    rw [this]
    refine (measurableSet_eq_fun hcardR measurable_const).inter
      ((measurableSet_le ?_ measurable_const).inter (measurableSet_lt measurable_const ?_))
    · exact measurable_fst.comp (measurable_snd.comp measurable_fst)
    · exact measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hpre : {ω | agedCnt S T t m ω = y} ∩ E = (fun ω => (Z ω, Lv ω)) ⁻¹' Q := by
    ext ω; simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, hQ, hE, agedCnt,
      Z, Lv]
  have hslice : ∀ z : (Fin m → ℝ) × ℝ × ℝ, (P.map Lv) (Prod.mk z ⁻¹' Q) =
      Set.indicator {z : (Fin m → ℝ) × ℝ × ℝ | z.2.1 ≤ t ∧ t < z.2.2}
        (fun z => Fg ν (Bset T t) y z.1) z := by
    intro z
    rw [Lv_law S m]
    by_cases hz : z.2.1 ≤ t ∧ t < z.2.2
    · rw [Set.indicator_of_mem (by exact hz), ← pi_count_g ν (Bset T t) hBm y z.1]
      congr 1
      ext l; simp only [Set.mem_preimage, hQ, Set.mem_setOf_eq, hz, and_true]
    · rw [Set.indicator_of_notMem (by exact hz)]
      have : Prod.mk z ⁻¹' Q = ∅ := by
        ext l; simp only [Set.mem_preimage, hQ, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro _ h1 h2; exact hz ⟨h1, h2⟩
      rw [this, measure_empty]
  have hEz : MeasurableSet {z : (Fin m → ℝ) × ℝ × ℝ | z.2.1 ≤ t ∧ t < z.2.2} :=
    (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))
  have hFm := Fg_meas ν (Bset T t) y hm1 hm2 (n := m)
  have step2 : P ({ω | agedCnt S T t m ω = y} ∩ E) = ∫⁻ ω in E, Fg ν (Bset T t) y (Tv ω) ∂P := by
    rw [hpre, ← Measure.map_apply (hZm.prodMk hLm) hQm,
      (indepFun_iff_map_prod_eq_prod_map_map hZm.aemeasurable hLm.aemeasurable).1
        (joint_indep S m), Measure.prod_apply hQm]
    simp_rw [hslice]
    rw [lintegral_map (f := {z : (Fin m → ℝ) × ℝ × ℝ | z.2.1 ≤ t ∧ t < z.2.2}.indicator
        (fun z => Fg ν (Bset T t) y z.1)) ((hFm.comp measurable_fst).indicator hEz) hZm,
      ← lintegral_indicator hEm]
    rfl
  rw [step2, setLIntegral_congr (E_eq_N S ht m)]
  have hmeasure : (P.restrict {ω | S.orderCount t ω = m}).map Tv =
      (P {ω | S.orderCount t ω = m} * ENNReal.ofReal ((Nat.factorial m : ℝ) / t ^ m)) •
        volume.restrict {x : Fin m → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t} := by
    ext A hA
    rw [Measure.map_apply hTm hA, Measure.restrict_apply (hTm hA), Measure.smul_apply,
      Measure.restrict_apply hA, smul_eq_mul, Set.inter_comm]
    exact (arrival_os_core S ht m hA).trans (mul_assoc _ _ _).symm
  rw [← lintegral_map hFm hTm, hmeasure, lintegral_smul_measure]
  congr 1
  have hs := sym_lintegral t (Fg ν (Bset T t) y) hFm (fun σ s => Fg_perm ν (Bset T t) y σ s)
  have hne : (Nat.factorial m : ENNReal) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  rw [box_integral_g ν (Bset T t) t y hm1 hm2, lint_B ν T ht, lint_Bc ν T ht] at hs
  rw [hs, ← mul_assoc, ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _), one_mul]

lemma IT_bounds [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (T : ℝ) {t : ℝ} (ht : 0 < t) :
    0 ≤ ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u ∧
      0 ≤ t - ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u := by
  haveI := nu_prob S
  have hint : IntervalIntegrable (hB (volume.withDensity S.density) T t) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le]; exact hB_integrable _ T t
  constructor
  · exact intervalIntegral.integral_nonneg ht.le (fun u _ => (hB_bounds _ T t u).1)
  · have : t - ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u =
        ∫ u in (0:ℝ)..t, (1 - hB (volume.withDensity S.density) T t u) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hint]; simp
    rw [this]
    exact intervalIntegral.integral_nonneg ht.le (fun u _ => sub_nonneg.2 (hB_bounds _ T t u).2)

theorem aged_binom_real [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (T : ℝ) {t : ℝ}
    (ht : 0 < t) (m y : ℕ) :
    (P ({ω | agedCnt S T t m ω = y} ∩ {ω | S.orderCount t ω = m})).toReal =
      (P {ω | S.orderCount t ω = m}).toReal *
        ((Nat.choose m y : ℝ) *
          ((1 / t) * ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u) ^ y *
          (1 - (1 / t) * ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u) ^ (m - y)) := by
  rw [aged_binom_enn S T ht m y]
  obtain ⟨hI0, hJ0⟩ := IT_bounds S T ht
  set I := ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u with hI
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (Nat.cast_nonneg _)
    (pow_nonneg ht.le _)), ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hI0, ENNReal.toReal_ofReal hJ0]
  rcases le_or_gt y m with hxn | hxn
  · have h1 : 1 - (1 / t) * I = (t - I) / t := by field_simp
    rw [h1]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hxn
    rw [Nat.add_sub_cancel_left]
    have hf : ((y + k).factorial : ℝ) ≠ 0 := by positivity
    have htn : t ≠ 0 := ht.ne'
    rw [div_pow, mul_pow, pow_add]
    simp only [one_div, inv_pow]
    field_simp
    try ring
  · rw [Nat.choose_eq_zero_of_lt hxn]; simp

/-! ### Compound system: independence and convolution -/

lemma cs_meas (S : CompoundResupplySystem Ω P) :
    ∀ i, Measurable (Sum.elim S.gap (Sum.elim S.resupply (fun k ω => (S.size k ω : ℝ))) i) := by
  rintro (k | k | k)
  · exact S.gap_measurable k
  · exact S.resupply_measurable k
  · exact (measurable_from_nat (f := fun j : ℕ => (j : ℝ))).comp (S.size_measurable k)

def eL : ℕ ↪ ℕ ⊕ (ℕ ⊕ ℕ) := ⟨fun k => Sum.inr (Sum.inl k), fun a b h => by simpa using h⟩
def eS : ℕ ↪ ℕ ⊕ (ℕ ⊕ ℕ) := ⟨fun k => Sum.inr (Sum.inr k), fun a b h => by simpa using h⟩

lemma block_indep [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) (m : ℕ) :
    IndepFun (fun ω => ((fun i : Fin m => S.arrival i ω), psum S.toResupplySystem m ω,
        psum S.toResupplySystem (m + 1) ω, (fun i : Fin m => S.resupply i ω)))
      (fun ω => fun i : Fin m => (S.size i ω : ℝ)) P := by
  classical
  let A : Finset (ℕ ⊕ (ℕ ⊕ ℕ)) :=
    (Finset.range (m + 1)).map (Function.Embedding.inl) ∪ (Finset.range m).map eL
  let B : Finset (ℕ ⊕ (ℕ ⊕ ℕ)) := (Finset.range m).map eS
  have hd : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [A, B, Finset.mem_union, Finset.mem_map, Finset.mem_range,
      Function.Embedding.inl_apply, eL, eS, Function.Embedding.coeFn_mk] at ha hb
    obtain ⟨j, -, rfl⟩ := hb
    rcases ha with ⟨k, -, hk⟩ | ⟨k, -, hk⟩ <;> cases hk
  have h := S.indep_all.indepFun_finset _ _ hd (cs_meas S)
  let get : (A → ℝ) → ℕ → ℝ := fun v k => if hk : Sum.inl k ∈ A then v ⟨Sum.inl k, hk⟩ else 0
  let getL : (A → ℝ) → ℕ → ℝ := fun v k =>
    if hk : Sum.inr (Sum.inl k) ∈ A then v ⟨Sum.inr (Sum.inl k), hk⟩ else 0
  have hget : ∀ k, Measurable (fun v : A → ℝ => get v k) := by
    intro k
    by_cases hk : Sum.inl k ∈ A
    · simp only [get, hk, dif_pos]; exact measurable_pi_apply _
    · simp only [get, hk, dif_neg, not_false_eq_true]; exact measurable_const
  have hgetL : ∀ k, Measurable (fun v : A → ℝ => getL v k) := by
    intro k
    by_cases hk : Sum.inr (Sum.inl k) ∈ A
    · simp only [getL, hk, dif_pos]; exact measurable_pi_apply _
    · simp only [getL, hk, dif_neg, not_false_eq_true]; exact measurable_const
  let φ : (A → ℝ) → (Fin m → ℝ) × ℝ × ℝ × (Fin m → ℝ) := fun v =>
    ((fun i : Fin m => ∑ k ∈ Finset.range (i.val + 1), get v k),
      ∑ k ∈ Finset.range m, get v k, ∑ k ∈ Finset.range (m + 1), get v k,
      fun i : Fin m => getL v i.val)
  have hφ : Measurable φ := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_))
    · exact measurable_pi_lambda _ (fun i => Finset.measurable_sum _ (fun k _ => hget k))
    · exact Finset.measurable_sum _ (fun k _ => hget k)
    · exact Finset.measurable_sum _ (fun k _ => hget k)
    · exact measurable_pi_lambda _ (fun i => hgetL i.val)
  have hmemB : ∀ i : Fin m, (Sum.inr (Sum.inr i.val) : ℕ ⊕ (ℕ ⊕ ℕ)) ∈ B := by
    intro i; exact Finset.mem_map.2 ⟨i.val, Finset.mem_range.2 i.isLt, rfl⟩
  have hψ : Measurable (fun v : B → ℝ => fun i : Fin m => v ⟨Sum.inr (Sum.inr i.val), hmemB i⟩) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  have h2 := h.comp hφ hψ
  have hg : ∀ ω, ∀ k, k < m + 1 →
      get (fun i : A => Sum.elim S.gap (Sum.elim S.resupply (fun k ω => (S.size k ω : ℝ))) i ω) k
        = S.gap k ω := by
    intro ω k hk
    have hm : Sum.inl k ∈ A :=
      Finset.mem_union_left _ (Finset.mem_map.2 ⟨k, Finset.mem_range.2 hk, rfl⟩)
    simp only [get, dif_pos hm]; rfl
  have hgL : ∀ ω, ∀ k, k < m →
      getL (fun i : A => Sum.elim S.gap (Sum.elim S.resupply (fun k ω => (S.size k ω : ℝ))) i ω) k
        = S.resupply k ω := by
    intro ω k hk
    have hm : Sum.inr (Sum.inl k) ∈ A :=
      Finset.mem_union_right _ (Finset.mem_map.2 ⟨k, Finset.mem_range.2 hk, rfl⟩)
    simp only [getL, dif_pos hm]; rfl
  convert h2 using 1
  · funext ω
    simp only [Function.comp_apply, φ]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
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
    · funext i
      simp only
      rw [hgL ω i.val i.isLt]
  · rfl

lemma sum_size_cast (S : CompoundResupplySystem Ω P) (A : Finset ℕ) (n : ℕ) :
    {ω | ∑ k ∈ A, S.size k ω = n} = {ω | ∑ k ∈ A, (S.size k ω : ℝ) = (n : ℝ)} := by
  ext ω; simp only [Set.mem_setOf_eq]; rw [← Nat.cast_sum, Nat.cast_inj]

lemma sum_size_meas (S : CompoundResupplySystem Ω P) (A : Finset ℕ) (n : ℕ) :
    MeasurableSet {ω | ∑ k ∈ A, S.size k ω = n} := by
  rw [sum_size_cast]
  exact measurableSet_eq_fun (Finset.measurable_sum _
    (fun k _ => (measurable_from_nat (f := fun j : ℕ => (j : ℝ))).comp (S.size_measurable k))) measurable_const

lemma size_law' (S : CompoundResupplySystem Ω P) (k j : ℕ) :
    P {ω | S.size k ω = j} = P {ω | S.size 0 ω = j} := by
  have h1 : {ω | S.size k ω = j} = S.size k ⁻¹' {j} := rfl
  have h2 : {ω | S.size 0 ω = j} = S.size 0 ⁻¹' {j} := rfl
  rw [h1, h2, ← Measure.map_apply (S.size_measurable k) (measurableSet_singleton j),
    ← Measure.map_apply (S.size_measurable 0) (measurableSet_singleton j), S.size_law k]

lemma conv_lemma [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) (A : Finset ℕ) :
    ∀ n, (P {ω | ∑ k ∈ A, S.size k ω = n}).toReal = convPow S.sizePMF A.card n := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    intro n
    simp only [Finset.sum_empty, Finset.card_empty, convPow]
    by_cases hn : n = 0
    · subst hn; simp
    · have : {ω : Ω | 0 = n} = ∅ := by ext; simp [Ne.symm hn]
      rw [this]; simp [hn]
  | insert a A ha ih =>
    intro n
    rw [Finset.card_insert_of_notMem ha, convPow]
    -- independence of the partial sum and the new size
    let B1 : Finset (ℕ ⊕ (ℕ ⊕ ℕ)) := A.map eS
    let B2 : Finset (ℕ ⊕ (ℕ ⊕ ℕ)) := {Sum.inr (Sum.inr a)}
    have hd : Disjoint B1 B2 := by
      rw [Finset.disjoint_singleton_right]
      intro hmem
      obtain ⟨x, hx, hxa⟩ := Finset.mem_map.1 hmem
      change Sum.inr (Sum.inr x) = Sum.inr (Sum.inr a) at hxa
      simp only [Sum.inr.injEq] at hxa
      exact ha (hxa ▸ hx)
    have hind := S.indep_all.indepFun_finset _ _ hd (cs_meas S)
    have hφ : Measurable (fun v : B1 → ℝ => ∑ i, v i) :=
      Finset.measurable_sum (f := fun (i : B1) (v : B1 → ℝ) => v i) _
        (fun i _ => measurable_pi_apply i)
    have hψ : Measurable (fun v : B2 → ℝ => v ⟨Sum.inr (Sum.inr a), Finset.mem_singleton_self _⟩) :=
      measurable_pi_apply _
    have h2 := hind.comp hφ hψ
    have hX : (fun ω => ∑ k ∈ A, (S.size k ω : ℝ)) = (fun v : B1 → ℝ => ∑ i, v i) ∘
        (fun ω (i : B1) => Sum.elim S.gap (Sum.elim S.resupply (fun k ω => (S.size k ω : ℝ))) i ω)
        := by
      funext ω
      simp only [Function.comp_apply]
      rw [Finset.sum_coe_sort B1 (fun i => Sum.elim S.gap (Sum.elim S.resupply
        (fun k ω => (S.size k ω : ℝ))) i ω), Finset.sum_map]
      rfl
    have hY : (fun ω => (S.size a ω : ℝ)) =
        (fun v : B2 → ℝ => v ⟨Sum.inr (Sum.inr a), Finset.mem_singleton_self _⟩) ∘
        (fun ω (i : B2) => Sum.elim S.gap (Sum.elim S.resupply (fun k ω => (S.size k ω : ℝ))) i ω)
        := rfl
    rw [← hX, ← hY] at h2
    -- decomposition of the event
    have hset : {ω | ∑ k ∈ insert a A, S.size k ω = n} =
        ⋃ j ∈ Finset.range (n + 1),
          ({ω | ∑ k ∈ A, (S.size k ω : ℝ) = (j : ℝ)} ∩
            {ω | (S.size a ω : ℝ) = ((n - j : ℕ) : ℝ)}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_range,
        exists_prop, Finset.sum_insert ha]
      constructor
      · intro h
        refine ⟨∑ k ∈ A, S.size k ω, by omega, by rw [Nat.cast_sum], ?_⟩
        rw [Nat.cast_inj]; omega
      · rintro ⟨j, hj, h1, h2⟩
        rw [← Nat.cast_sum, Nat.cast_inj] at h1
        rw [Nat.cast_inj] at h2
        omega
    have hmeasX : Measurable (fun ω => ∑ k ∈ A, (S.size k ω : ℝ)) :=
      Finset.measurable_sum _ (fun k _ => (measurable_from_nat (f := fun j : ℕ => (j : ℝ))).comp (S.size_measurable k))
    have hmeasY : Measurable (fun ω => (S.size a ω : ℝ)) :=
      (measurable_from_nat (f := fun j : ℕ => (j : ℝ))).comp (S.size_measurable a)
    rw [hset, measure_biUnion_finset]
    · rw [ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have := h2.measure_inter_preimage_eq_mul {(j : ℝ)} {((n - j : ℕ) : ℝ)}
        (measurableSet_singleton _) (measurableSet_singleton _)
      simp only [Set.preimage, Set.mem_singleton_iff] at this
      rw [this, ENNReal.toReal_mul, ← sum_size_cast, ih j]
      congr 1
      have e : {ω | (S.size a ω : ℝ) = ((n - j : ℕ) : ℝ)} = {ω | S.size a ω = n - j} := by
        ext ω; simp only [Set.mem_setOf_eq, Nat.cast_inj]
      rw [e, size_law']
      rfl
    · intro i _ j _ hij
      rw [Function.onFun, Set.disjoint_left]
      rintro ω ⟨h1, -⟩ ⟨h2, -⟩
      apply hij
      exact_mod_cast h1.symm.trans h2
    · intro j _
      exact (measurableSet_eq_fun hmeasX measurable_const).inter
        (measurableSet_eq_fun hmeasY measurable_const)

/-! ### Compound system: decomposition over the aged orders -/

open Classical in
noncomputable def agedSet (S : ResupplySystem Ω P) (T t : ℝ) (m : ℕ) (ω : Ω) : Finset (Fin m) :=
  Finset.univ.filter (fun i : Fin m => S.resupply i ω ∈ Bset T t (S.arrival i ω))

lemma agedCnt_eq (S : ResupplySystem Ω P) (T t : ℝ) (m : ℕ) (ω : Ω) :
    agedCnt S T t m ω = (agedSet S T t m ω).card := rfl

open Classical in
lemma aged_units_eq (S : CompoundResupplySystem Ω P) {T t : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hω : ∀ k, 0 ≤ S.gap k ω) {m : ℕ}
    (h : psum S.toResupplySystem m ω ≤ t ∧ t < psum S.toResupplySystem (m + 1) ω) :
    S.agedUnitsInResupply T t ω = ∑ i ∈ agedSet S.toResupplySystem T t m ω, S.size i ω := by
  have hset : {k : ℕ | S.arrival k ω + T ≤ t ∧ t < S.arrival k ω + S.resupply k ω} =
      ↑((Finset.range m).filter
        (fun k => S.resupply k ω ∈ Bset T t (S.arrival k ω))) := by
    ext k
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, Bset]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1, h2⟩
      by_contra hk; push_neg at hk
      have := psum_mono S.toResupplySystem hω (show m + 1 ≤ k + 1 by omega)
      have e : S.arrival k ω = psum S.toResupplySystem (k + 1) ω := rfl
      linarith [h.2]
    · rintro ⟨_, h1, h2⟩
      exact ⟨h1, h2⟩
  unfold CompoundResupplySystem.agedUnitsInResupply agedSet
  rw [hset, finsum_mem_coe_finset, Finset.sum_filter, Finset.sum_filter]
  exact (Fin.sum_univ_eq_sum_range
    (fun k => if S.resupply k ω ∈ Bset T t (S.arrival k ω) then S.size k ω else 0) m).symm

theorem comp_decomp [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) {T t : ℝ}
    (hT : 0 ≤ T) (ht : 0 < t) (m n : ℕ) :
    P ({ω | S.agedUnitsInResupply T t ω = n} ∩ {ω | S.orderCount t ω = m}) =
      ∑ y ∈ Finset.range (m + 1), ENNReal.ofReal (convPow S.sizePMF y n) *
        P ({ω | agedCnt S.toResupplySystem T t m ω = y} ∩ {ω | S.orderCount t ω = m}) := by
  classical
  set R := S.toResupplySystem with hR
  set E := {ω | psum R m ω ≤ t ∧ t < psum R (m + 1) ω} with hE
  have h1 : ({ω | S.agedUnitsInResupply T t ω = n} ∩ {ω | S.orderCount t ω = m} : Set Ω) =ᵐ[P]
      ({ω | ∑ i ∈ agedSet R T t m ω, S.size i ω = n} ∩ E : Set Ω) := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [gap_nonneg_ae R, finite_ae R ht.le] with ω hω hK
    show (S.agedUnitsInResupply T t ω = n ∧ R.orderCount t ω = m) ↔
      (∑ i ∈ agedSet R T t m ω, S.size i ω = n ∧ (psum R m ω ≤ t ∧ t < psum R (m + 1) ω))
    rw [count_iff R ht.le hω hK m]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(aged_units_eq S hT hω h2) ▸ h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(aged_units_eq S hT hω h2).symm ▸ h1, h2⟩
  rw [measure_congr h1]
  rw [Finset.sum_congr rfl (fun y _ => by
    rw [measure_congr ((ae_eq_refl {ω | agedCnt R T t m ω = y}).inter (E_eq_N R ht m).symm)])]
  simp only [← hE]
  -- the two random vectors
  set V1 := fun ω => ((fun i : Fin m => S.arrival i ω), psum R m ω, psum R (m + 1) ω,
    (fun i : Fin m => S.resupply i ω)) with hV1
  set V2 := fun ω => fun i : Fin m => (S.size i ω : ℝ) with hV2
  have hind : IndepFun V1 V2 P := block_indep S m
  let M1 : Finset (Fin m) → Set ((Fin m → ℝ) × ℝ × ℝ × (Fin m → ℝ)) := fun A =>
    {z | (∀ i, (z.2.2.2 i ∈ Bset T t (z.1 i) ↔ i ∈ A)) ∧ z.2.1 ≤ t ∧ t < z.2.2.1}
  let M2 : Finset (Fin m) → Set (Fin m → ℝ) := fun A => {w | ∑ i ∈ A, w i = (n : ℝ)}
  have hM1 : ∀ A, MeasurableSet (M1 A) := by
    intro A
    have hfi : ∀ i, Measurable (fun z : (Fin m → ℝ) × ℝ × ℝ × (Fin m → ℝ) => z.1 i) :=
      fun i => (measurable_pi_apply i).comp measurable_fst
    have hli : ∀ i, Measurable (fun z : (Fin m → ℝ) × ℝ × ℝ × (Fin m → ℝ) => z.2.2.2 i) :=
      fun i => (measurable_pi_apply i).comp
        (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hPi : ∀ i, MeasurableSet
        {z : (Fin m → ℝ) × ℝ × ℝ × (Fin m → ℝ) | z.2.2.2 i ∈ Bset T t (z.1 i)} := by
      intro i
      have : {z : (Fin m → ℝ) × ℝ × ℝ × (Fin m → ℝ) | z.2.2.2 i ∈ Bset T t (z.1 i)} =
          {z | z.1 i + T ≤ t} ∩ {z | t < z.1 i + z.2.2.2 i} := by
        ext z; simp [Bset]
      rw [this]
      exact (measurableSet_le ((hfi i).add measurable_const) measurable_const).inter
        (measurableSet_lt measurable_const ((hfi i).add (hli i)))
    have : M1 A = (⋂ i, {z : (Fin m → ℝ) × ℝ × ℝ × (Fin m → ℝ) |
        (z.2.2.2 i ∈ Bset T t (z.1 i) ↔ i ∈ A)}) ∩ ({z | z.2.1 ≤ t} ∩ {z | t < z.2.2.1}) := by
      ext z; simp only [M1, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [this]
    refine (MeasurableSet.iInter fun i => ?_).inter
      ((measurableSet_le ?_ measurable_const).inter (measurableSet_lt measurable_const ?_))
    · by_cases hi : i ∈ A
      · simp only [hi, iff_true]; exact hPi i
      · simp only [hi, iff_false]; exact (hPi i).compl
    · exact measurable_fst.comp (measurable_snd)
    · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hM2 : ∀ A, MeasurableSet (M2 A) := fun A =>
    measurableSet_eq_fun (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))
      measurable_const
  have pre1 : ∀ A, {ω | agedSet R T t m ω = A} ∩ E = V1 ⁻¹' M1 A := by
    intro A
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, M1, V1, hE,
      Finset.ext_iff, agedSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have pre2 : ∀ A : Finset (Fin m), {ω | ∑ i ∈ A, S.size i ω = n} = V2 ⁻¹' M2 A := by
    intro A
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, M2, V2]
    rw [← Nat.cast_sum, Nat.cast_inj]
  have hdec : {ω | ∑ i ∈ agedSet R T t m ω, S.size i ω = n} ∩ E =
      ⋃ A ∈ (Finset.univ : Finset (Finset (Fin m))), (V1 ⁻¹' M1 A ∩ V2 ⁻¹' M2 A) := by
    ext ω
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, ← pre1, ← pre2,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, ⟨rfl, h2⟩, h1⟩
    · rintro ⟨A, ⟨rfl, h2⟩, h1⟩; exact ⟨h1, h2⟩
  have hV1m : Measurable V1 := (Tv_meas R m).prodMk ((psum_meas R m).prodMk
    ((psum_meas R (m + 1)).prodMk
      (measurable_pi_lambda _ (fun i => S.resupply_measurable i.val))))
  have hV2m : Measurable V2 := measurable_pi_lambda _
    (fun i => (measurable_from_nat (f := fun j : ℕ => (j : ℝ))).comp (S.size_measurable i.val))
  have hconv : ∀ A : Finset (Fin m), P (V2 ⁻¹' M2 A) = ENNReal.ofReal (convPow S.sizePMF A.card n) := by
    intro A
    have hc := conv_lemma S (A.map Fin.valEmbedding) n
    rw [Finset.card_map] at hc
    rw [← pre2, ← hc, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    congr 1
    ext ω; simp only [Set.mem_setOf_eq, Finset.sum_map, Fin.valEmbedding_apply]
  rw [hdec, measure_biUnion_finset]
  · simp_rw [hind.measure_inter_preimage_eq_mul _ _ (hM1 _) (hM2 _), hconv]
    -- regroup by the cardinality
    have hy : ∀ y ∈ Finset.range (m + 1),
        P ({ω | agedCnt R T t m ω = y} ∩ E) =
          ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))) with A.card = y, P (V1 ⁻¹' M1 A) := by
      intro y _
      have : {ω | agedCnt R T t m ω = y} ∩ E =
          ⋃ A ∈ ((Finset.univ : Finset (Finset (Fin m))).filter (fun A => A.card = y)),
            V1 ⁻¹' M1 A := by
        ext ω
        simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, ← pre1,
          Set.mem_inter_iff, Set.mem_setOf_eq, agedCnt_eq, exists_prop]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨_, h1, rfl, h2⟩
        · rintro ⟨A, hA, rfl, h2⟩; exact ⟨hA, h2⟩
      rw [this, measure_biUnion_finset]
      · intro A _ B _ hAB
        rw [Function.onFun, Set.disjoint_left]
        intro ω h1 h2
        rw [← pre1] at h1 h2
        exact hAB (h1.1.symm.trans h2.1)
      · intro A _; exact hV1m (hM1 A)
    have hRHS : ∑ y ∈ Finset.range (m + 1), ENNReal.ofReal (convPow S.sizePMF y n) *
        P ({ω | agedCnt R T t m ω = y} ∩ E) =
        ∑ y ∈ Finset.range (m + 1), ∑ A ∈ (Finset.univ : Finset (Finset (Fin m))) with A.card = y,
          ENNReal.ofReal (convPow S.sizePMF y n) * P (V1 ⁻¹' M1 A) :=
      Finset.sum_congr rfl (fun y hy' => by rw [hy y hy', Finset.mul_sum])
    rw [hRHS]
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (g := Finset.card)
      (t := Finset.range (m + 1))
      (fun A _ => by
        rw [Finset.mem_range]
        have := Finset.card_le_univ A
        rw [Fintype.card_fin] at this; omega)]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun A hA => ?_))
    rw [Finset.mem_filter] at hA
    rw [hA.2, mul_comm]
  · intro A _ B _ hAB
    rw [Function.onFun, Set.disjoint_left]
    intro ω h1 h2
    rw [← pre1] at h1 h2
    exact hAB (h1.1.1.symm.trans h2.1.1)
  · intro A _
    exact (hV1m (hM1 A)).inter (hV2m (hM2 A))

/-! ### Compound system: finite-time law and the limit -/

lemma thin_hasSum (a p : ℝ) (x : ℕ) :
    HasSum (fun n : ℕ => Real.exp (-a) * a ^ n / (Nat.factorial n : ℝ) *
      ((Nat.choose n x : ℝ) * p ^ x * (1 - p) ^ (n - x)))
      (Real.exp (-(a * p)) * (a * p) ^ x / (Nat.factorial x : ℝ)) := by
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

lemma convPow_eq_zero {u : ℕ → ℝ} (hu : u 0 = 0) : ∀ y n, n < y → convPow u y n = 0 := by
  intro y
  induction y with
  | zero => intro n h; omega
  | succ y ih =>
    intro n hn
    rw [convPow]
    refine Finset.sum_eq_zero (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    rcases Nat.lt_or_ge j n with h | h
    · rw [ih j (by omega), zero_mul]
    · have : n - j = 0 := by omega
      rw [this, hu, mul_zero]

lemma sizePMF_zero (S : CompoundResupplySystem Ω P) : S.sizePMF 0 = 0 := by
  unfold CompoundResupplySystem.sizePMF
  have : {ω | S.size 0 ω = 0} = ∅ := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    have := S.size_pos 0 ω; omega
  rw [this]; simp

lemma convPow_nonneg {u : ℕ → ℝ} (hu : ∀ j, 0 ≤ u j) : ∀ y n, 0 ≤ convPow u y n := by
  intro y
  induction y with
  | zero => intro n; simp only [convPow]; split_ifs <;> norm_num
  | succ y ih =>
    intro n
    simp only [convPow]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (ih j) (hu _))

open Classical in
lemma aged_sum_meas (S : CompoundResupplySystem Ω P) (T t : ℝ) (m : ℕ) :
    Measurable (fun ω => ((∑ i ∈ agedSet S.toResupplySystem T t m ω, S.size i ω : ℕ) : ℝ)) := by
  unfold agedSet
  simp_rw [Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  refine Finset.measurable_sum _ (fun i _ => Measurable.ite ?_
    ((measurable_from_nat (f := fun j : ℕ => (j : ℝ))).comp (S.size_measurable i.val))
    measurable_const)
  have : {ω | S.resupply i ω ∈ Bset T t (S.arrival i ω)} =
      {ω | S.arrival i ω + T ≤ t} ∩ {ω | t < S.arrival i ω + S.resupply i ω} := by
    ext ω; simp [Bset]
  rw [this]
  exact (measurableSet_le ((psum_meas S.toResupplySystem _).add measurable_const)
    measurable_const).inter
    (measurableSet_lt measurable_const ((psum_meas S.toResupplySystem _).add
      (S.resupply_measurable _)))

theorem comp_finite [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) {T t : ℝ}
    (hT : 0 ≤ T) (ht : 0 < t) (n : ℕ) :
    (P {ω | S.agedUnitsInResupply T t ω = n}).toReal =
      compoundPoissonPMF (S.rate * ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u)
        S.sizePMF n := by
  classical
  set R := S.toResupplySystem with hR
  set I := ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u with hI
  set f : ℕ → Set Ω := fun m => {ω | S.agedUnitsInResupply T t ω = n} ∩ {ω | S.orderCount t ω = m}
    with hf
  have hU : {ω | S.agedUnitsInResupply T t ω = n} = ⋃ m, f m := by
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
  have hnm : ∀ m, NullMeasurableSet (f m) P := by
    intro m
    have h1 : (f m : Set Ω) =ᵐ[P]
        ({ω | ∑ i ∈ agedSet R T t m ω, S.size i ω = n} ∩
          {ω | psum R m ω ≤ t ∧ t < psum R (m + 1) ω} : Set Ω) := by
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [gap_nonneg_ae R, finite_ae R ht.le] with ω hω hK
      show (S.agedUnitsInResupply T t ω = n ∧ R.orderCount t ω = m) ↔
        (∑ i ∈ agedSet R T t m ω, S.size i ω = n ∧ (psum R m ω ≤ t ∧ t < psum R (m + 1) ω))
      rw [count_iff R ht.le hω hK m]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(aged_units_eq S hT hω h2) ▸ h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨(aged_units_eq S hT hω h2).symm ▸ h1, h2⟩
    refine NullMeasurableSet.congr ?_ h1.symm
    refine MeasurableSet.nullMeasurableSet ?_
    have : {ω | ∑ i ∈ agedSet R T t m ω, S.size i ω = n} =
        {ω | ((∑ i ∈ agedSet R T t m ω, S.size i ω : ℕ) : ℝ) = (n : ℝ)} := by
      ext ω; simp only [Set.mem_setOf_eq, Nat.cast_inj]
    rw [this]
    exact (measurableSet_eq_fun (aged_sum_meas S T t m) measurable_const).inter
      ((measurableSet_le (psum_meas R m) measurable_const).inter
        (measurableSet_lt measurable_const (psum_meas R (m + 1))))
  rw [hU, measure_iUnion₀ hdisj hnm, ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)]
  have hterm : ∀ m, (P (f m)).toReal = ∑ y ∈ Finset.range (n + 1), convPow S.sizePMF y n *
      (Real.exp (-(S.rate * t)) * (S.rate * t) ^ m / (Nat.factorial m : ℝ) *
        ((Nat.choose m y : ℝ) * ((1 / t) * I) ^ y * (1 - (1 / t) * I) ^ (m - y))) := by
    intro m
    simp only [hf]
    rw [comp_decomp S hT ht m n, ENNReal.toReal_sum (fun y _ => ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (measure_ne_top _ _))]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal', aged_binom_real S.toResupplySystem T ht m,
      order_count_core S.toResupplySystem ht]
    have hz : ∀ y, n < y ∨ m < y → max (convPow S.sizePMF y n) 0 *
        (Real.exp (-(S.rate * t)) * (S.rate * t) ^ m / (Nat.factorial m : ℝ) *
          ((Nat.choose m y : ℝ) * ((1 / t) * I) ^ y * (1 - (1 / t) * I) ^ (m - y))) = 0 := by
      intro y hy
      rcases hy with hy | hy
      · rw [convPow_eq_zero (sizePMF_zero S) y n hy]; simp
      · rw [Nat.choose_eq_zero_of_lt hy]; simp
    have hz' : ∀ y, n < y ∨ m < y → convPow S.sizePMF y n *
        (Real.exp (-(S.rate * t)) * (S.rate * t) ^ m / (Nat.factorial m : ℝ) *
          ((Nat.choose m y : ℝ) * ((1 / t) * I) ^ y * (1 - (1 / t) * I) ^ (m - y))) = 0 := by
      intro y hy
      rcases hy with hy | hy
      · rw [convPow_eq_zero (sizePMF_zero S) y n hy]; simp
      · rw [Nat.choose_eq_zero_of_lt hy]; simp
    have hmax : ∀ y, max (convPow S.sizePMF y n) 0 = convPow S.sizePMF y n := by
      intro y
      rcases le_or_gt y n with hyn | hyn
      · have : 0 ≤ convPow S.sizePMF y n :=
          convPow_nonneg (fun j => ENNReal.toReal_nonneg) y n
        exact max_eq_left this
      · rw [convPow_eq_zero (sizePMF_zero S) y n hyn]; simp
    simp only [hmax]
    simp only [← hI]
    have hN : n + 1 ≤ max (m + 1) (n + 1) := le_max_right _ _
    have hM : m + 1 ≤ max (m + 1) (n + 1) := le_max_left _ _
    rw [Finset.sum_subset (Finset.range_subset_range.2 hM) (fun y hy hy' => by
        simp only [Finset.mem_range] at hy hy'
        exact hz' y (Or.inr (by omega))),
      Finset.sum_subset (Finset.range_subset_range.2 hN) (fun y hy hy' => by
        simp only [Finset.mem_range] at hy hy'
        exact hz' y (Or.inl (by omega)))]
    try (refine Finset.sum_congr rfl (fun y _ => ?_); ring)
  simp only [hterm]
  refine HasSum.tsum_eq ?_
  unfold compoundPoissonPMF
  have hap : S.rate * I = (S.rate * t) * ((1 / t) * I) := by field_simp
  rw [hap]
  have hv : ∀ y, Real.exp (-((S.rate * t) * ((1 / t) * I))) * ((S.rate * t) * ((1 / t) * I)) ^ y /
      (Nat.factorial y : ℝ) * convPow S.sizePMF y n = convPow S.sizePMF y n *
      (Real.exp (-((S.rate * t) * ((1 / t) * I))) * ((S.rate * t) * ((1 / t) * I)) ^ y /
        (Nat.factorial y : ℝ)) := fun y => by ring
  simp only [hv]
  exact hasSum_sum (fun y _ =>
    (thin_hasSum (S.rate * t) ((1 / t) * I) y).mul_left (convPow S.sizePMF y n))

lemma one_sub_cdf (S : ResupplySystem Ω P) [IsProbabilityMeasure P] (u : ℝ) :
    1 - S.resupplyCdf u = (P {ω | u < S.resupply 0 ω}).toReal := by
  unfold ResupplySystem.resupplyCdf
  have hc : {ω | u < S.resupply 0 ω} = {ω | S.resupply 0 ω ≤ u}ᶜ := by
    ext ω; simp
  rw [hc, prob_compl_eq_one_sub (measurableSet_le (S.resupply_measurable 0) measurable_const),
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]

lemma tail_integrable [IsProbabilityMeasure P] (S : ResupplySystem Ω P) :
    IntegrableOn (fun u => 1 - S.resupplyCdf u) (Set.Ioi 0) := by
  simp_rw [one_sub_cdf]
  have hL := lintegral_eq_lintegral_meas_lt P
    (Eventually.of_forall (fun ω => S.resupply_nonneg 0 ω))
    (S.resupply_measurable 0).aemeasurable
  have hfin : ∫⁻ ω, ENNReal.ofReal (S.resupply 0 ω) ∂P < ⊤ :=
    S.resupply_integrable.lintegral_lt_top
  rw [hL] at hfin
  refine integrable_toReal_of_lintegral_ne_top ?_ hfin.ne
  exact (Antitone.measurable (fun a b hab => measure_mono (fun ω (h : b < S.resupply 0 ω) =>
    show a < S.resupply 0 ω from lt_of_le_of_lt hab h))).aemeasurable

lemma tail_integral [IsProbabilityMeasure P] (S : ResupplySystem Ω P) :
    ∫ u in Set.Ioi 0, (1 - S.resupplyCdf u) = S.meanResupply := by
  unfold ResupplySystem.meanResupply
  rw [Integrable.integral_eq_integral_meas_lt S.resupply_integrable
    (Eventually.of_forall (fun ω => S.resupply_nonneg 0 ω))]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [one_sub_cdf]; rfl

lemma IT_eq [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (T t : ℝ) :
    ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u =
      ∫ v in (0:ℝ)..t, (Set.Ici T).indicator (fun v => 1 - S.resupplyCdf v) v := by
  have : ∀ u, hB (volume.withDensity S.density) T t u =
      (Set.Ici T).indicator (fun v => 1 - S.resupplyCdf v) (t - u) := by
    intro u
    simp only [hB, Set.indicator, Set.mem_Ici, cdf_eq]
    by_cases h : u + T ≤ t
    · rw [if_pos h, if_pos (by linarith)]
    · rw [if_neg h, if_neg (by intro h'; apply h; linarith)]
  simp_rw [this]
  rw [intervalIntegral.integral_comp_sub_left (fun v => (Set.Ici T).indicator
    (fun v => 1 - S.resupplyCdf v) v) t]
  simp

lemma IT_tendsto [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun t => ∫ u in (0:ℝ)..t, hB (volume.withDensity S.density) T t u) atTop
      (𝓝 (∫ u in Set.Ioi T, (1 - S.resupplyCdf u))) := by
  simp_rw [IT_eq]
  have hint : IntegrableOn ((Set.Ici T).indicator (fun v => 1 - S.resupplyCdf v)) (Set.Ioi 0) :=
    (tail_integrable S).indicator measurableSet_Ici
  have h : Tendsto (fun t => ∫ v in (0:ℝ)..t, (Set.Ici T).indicator
      (fun v => 1 - S.resupplyCdf v) v) atTop
      (𝓝 (∫ v in Set.Ioi 0, (Set.Ici T).indicator (fun v => 1 - S.resupplyCdf v) v)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have hval : ∫ v in Set.Ioi 0, (Set.Ici T).indicator (fun v => 1 - S.resupplyCdf v) v =
      ∫ u in Set.Ioi T, (1 - S.resupplyCdf u) := by
    rw [setIntegral_indicator measurableSet_Ici]
    refine setIntegral_congr_set ?_
    rcases hT.eq_or_lt with h0 | h0
    · subst h0
      have : Set.Ioi (0:ℝ) ∩ Set.Ici 0 = Set.Ioi 0 := by
        ext v; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
        constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, h.le⟩
      rw [this]
      try exact Filter.EventuallyEq.rfl
    · have : Set.Ioi (0:ℝ) ∩ Set.Ici T = Set.Ici T := by
        ext v; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨by linarith, h⟩
      rw [this]
      exact Ioi_ae_eq_Ici.symm
  rw [← hval]; exact h

lemma cPP_continuous (u : ℕ → ℝ) (n : ℕ) : Continuous (fun μ => compoundPoissonPMF μ u n) := by
  unfold compoundPoissonPMF
  fun_prop

theorem aged_limit [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) {T : ℝ}
    (hT : 0 ≤ T) (n : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.agedUnitsInResupply T t ω = n}).toReal) atTop
      (𝓝 (compoundPoissonPMF (S.rate * ∫ u in Set.Ioi T, (1 - S.resupplyCdf u))
        S.sizePMF n)) := by
  have h1 := ((cPP_continuous S.sizePMF n).tendsto _).comp
    ((IT_tendsto S.toResupplySystem hT).const_mul S.rate)
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  exact (comp_finite S hT ht n).symm

theorem delayed_core [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) {T : ℝ}
    (hT : 0 ≤ T) (n : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.agedUnitsInResupply T t ω = n}).toReal) atTop
      (𝓝 (compoundPoissonPMF
        (S.rate * S.meanResupply *
          ((1 / S.meanResupply) * ∫ u in Set.Ioi T, (1 - S.resupplyCdf u)))
        S.sizePMF n)) := by
  have h := aged_limit S hT n
  convert h using 3
  by_cases hm : S.meanResupply = 0
  · have hK : ∫ u in Set.Ioi T, (1 - S.resupplyCdf u) = 0 := by
      have hle : ∫ u in Set.Ioi T, (1 - S.resupplyCdf u) ≤
          ∫ u in Set.Ioi 0, (1 - S.resupplyCdf u) := by
        refine setIntegral_mono_set (tail_integrable S.toResupplySystem) ?_ ?_
        · exact Eventually.of_forall (fun u => sub_nonneg.2 (cdf_bounds S.toResupplySystem u).2)
        · exact Eventually.of_forall (fun u (hu : u ∈ Set.Ioi T) =>
            show u ∈ Set.Ioi (0:ℝ) from lt_of_le_of_lt hT hu)
      have hge : 0 ≤ ∫ u in Set.Ioi T, (1 - S.resupplyCdf u) :=
        setIntegral_nonneg measurableSet_Ioi
          (fun u _ => sub_nonneg.2 (cdf_bounds S.toResupplySystem u).2)
      have := tail_integral S.toResupplySystem
      have hm' : S.toResupplySystem.meanResupply = 0 := hm
      linarith
    rw [hK, hm]; simp
  · field_simp

theorem compound_core [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) (n : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.unitsInResupply t ω = n}).toReal) atTop
      (𝓝 (compoundPoissonPMF (S.rate * S.meanResupply) S.sizePMF n)) := by
  have h := aged_limit S le_rfl n
  have e1 : ∀ t ω, S.unitsInResupply t ω = S.agedUnitsInResupply 0 t ω := by
    intro t ω
    unfold CompoundResupplySystem.unitsInResupply CompoundResupplySystem.agedUnitsInResupply
    simp only [add_zero]
  simp_rw [e1]
  rw [show S.meanResupply = ∫ u in Set.Ioi 0, (1 - S.resupplyCdf u) from
    (tail_integral S.toResupplySystem).symm]
  exact h
end ServiceParts.Palm

open ServiceParts.Palm


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : CompoundResupplySystem Ω P) (n : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.unitsInResupply t ω = n}).toReal) atTop
      (𝓝 (compoundPoissonPMF (S.rate * S.meanResupply) S.sizePMF n)) := by
  exact compound_core S n
