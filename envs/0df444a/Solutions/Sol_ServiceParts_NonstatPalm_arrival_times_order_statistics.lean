-- Prove2me | solution 1 for ServiceParts.NonstatPalm.arrival_times_order_statistics
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:18:27.210504+00:00
-- url     : https://prove2.me/submissions/297117c6-888f-4ec2-bf9c-e4eeb746d3d5

import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_ResupplySystem

open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.NonstatPalm

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


section Gen
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- partial sums `g 0 + ... + g (m-1)` -/
noncomputable def psumG (g : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range m, g i ω

lemma psumG_meas {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k)) (m : ℕ) :
    Measurable (psumG g m) := by
  unfold psumG
  exact Finset.measurable_sum _ (fun i _ => hm i)

lemma psumG_indep [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    (hi : iIndepFun g P) (m : ℕ) :
    IndepFun (psumG g m) (g m) P := by
  have hd : Disjoint (Finset.range m) ({m} : Finset ℕ) := by
    rw [Finset.disjoint_singleton_right]; simp
  have := hi.indepFun_finset _ _ hd hm
  have hφ : Measurable (fun v : (Finset.range m) → ℝ => ∑ i, v i) :=
    Finset.measurable_sum (f := fun (i : Finset.range m) (v : Finset.range m → ℝ) => v i) _
      (fun i _ => measurable_pi_apply i)
  have hψ : Measurable (fun v : ({m} : Finset ℕ) → ℝ =>
      v ⟨m, Finset.mem_singleton_self _⟩) := measurable_pi_apply _
  have h2 := this.comp hφ hψ
  convert h2 using 1
  · funext ω
    simp only [Function.comp_apply, psumG]
    rw [Finset.sum_coe_sort (Finset.range m) (fun i => g i ω)]
  · rfl

lemma psumG_surv [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    (hl : ∀ k, P.map (g k) = expMeasure 1) (hi : iIndepFun g P) (m : ℕ) (s : ℝ) :
    P {ω | s < psumG g m ω} = ENNReal.ofReal (surv 1 m s) := by
  induction m generalizing s with
  | zero =>
    simp only [psumG, Finset.range_zero, Finset.sum_empty, surv, Finset.sum_empty, mul_zero]
    split_ifs with h
    · simp [h]
    · simp [h]
  | succ m ih =>
    have e : {ω | s < psumG g (m + 1) ω} = {ω | s < psumG g m ω + g m ω} := by
      ext ω; simp [psumG, Finset.sum_range_succ]
    rw [e, step_law (psumG_meas hm m) (hm m) (psumG_indep hm hi m) one_pos
      (hl m) (surv 1 m) (surv_meas _ _) (surv_nonneg one_pos m)
      (surv_le_one one_pos m) ih s, surv_integral one_pos]

lemma psumG_mono {g : ℕ → Ω → ℝ} {ω : Ω} (hω : ∀ k, 0 ≤ g k ω) {i j : ℕ}
    (hij : i ≤ j) : psumG g i ω ≤ psumG g j ω := by
  unfold psumG
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hij)
    (fun k _ _ => hω k)

/-- number of points of the unit process in `[0, c]` -/
noncomputable def cntG (g : ℕ → Ω → ℝ) (c : ℝ) (ω : Ω) : ℕ :=
  {k : ℕ | psumG g (k + 1) ω ≤ c}.ncard

lemma cntG_iff {g : ℕ → Ω → ℝ} {t : ℝ} (ht : 0 ≤ t) {ω : Ω}
    (hω : ∀ k, 0 ≤ g k ω) (hK : ∃ K, t < psumG g K ω) (n : ℕ) :
    cntG g t ω = n ↔ psumG g n ω ≤ t ∧ t < psumG g (n + 1) ω := by
  obtain ⟨K, hK⟩ := hK
  have hfin : {k : ℕ | psumG g (k + 1) ω ≤ t}.Finite := by
    refine (Finset.finite_toSet (Finset.range K)).subset (fun k hk => ?_)
    simp only [Set.mem_setOf_eq] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h; push_neg at h
    have := psumG_mono hω (show K ≤ k + 1 by omega)
    linarith
  unfold cntG
  constructor
  · intro hc
    by_contra hneg
    rw [not_and_or, not_le, not_lt] at hneg
    rcases hneg with h | h
    · have hn : 1 ≤ n := by
        by_contra h0; push_neg at h0
        have : n = 0 := by omega
        subst this; simp [psumG] at h; linarith
      have hsub : {k : ℕ | psumG g (k + 1) ω ≤ t} ⊆ ↑(Finset.range (n - 1)) := by
        intro k hk
        simp only [Set.mem_setOf_eq] at hk
        simp only [Finset.coe_range, Set.mem_Iio]
        by_contra h'; push_neg at h'
        have := psumG_mono hω (show n ≤ k + 1 by omega)
        linarith
      have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset, Finset.card_range, hc] at this
      omega
    · have hsub : (↑(Finset.range (n + 1)) : Set ℕ) ⊆ {k : ℕ | psumG g (k + 1) ω ≤ t} := by
        intro k hk
        simp only [Finset.coe_range, Set.mem_Iio] at hk
        simp only [Set.mem_setOf_eq]
        have := psumG_mono hω (show k + 1 ≤ n + 1 by omega)
        linarith
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset, Finset.card_range, hc] at this
      omega
  · rintro ⟨h1, h2⟩
    have : {k : ℕ | psumG g (k + 1) ω ≤ t} = ↑(Finset.range n) := by
      ext k
      simp only [Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
      constructor
      · intro hk; by_contra h'; push_neg at h'
        have := psumG_mono hω (show n + 1 ≤ k + 1 by omega)
        linarith
      · intro hk
        have := psumG_mono hω (show k + 1 ≤ n by omega)
        linarith
    rw [this, Set.ncard_coe_finset, Finset.card_range]

lemma gapG_nonneg_ae [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    (hl : ∀ k, P.map (g k) = expMeasure 1) :
    ∀ᵐ ω ∂P, ∀ k, 0 ≤ g k ω := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have : {ω | ¬ 0 ≤ g k ω} = g k ⁻¹' Set.Iio 0 := by ext; simp
  rw [this, ← Measure.map_apply (hm k) measurableSet_Iio, hl k]
  haveI := isProbabilityMeasure_expMeasure (one_pos (α := ℝ))
  refine le_antisymm ?_ bot_le
  calc expMeasure 1 (Set.Iio 0) ≤ expMeasure 1 (Set.Iic 0) :=
        measure_mono Set.Iio_subset_Iic_self
    _ = ENNReal.ofReal (cdf (expMeasure 1) 0) := (ofReal_cdf _ _).symm
    _ = 0 := by rw [cdf_expMeasure_eq one_pos, if_pos le_rfl]; simp

lemma surv_tendsto {r : ℝ} {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m => surv r m t) atTop (𝓝 1) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (r * t)).tendsto_sum_nat
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.const_mul (Real.exp (-(r * t)))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h2
  refine h2.congr (fun m => ?_)
  rw [surv, if_neg (not_lt.2 ht)]

lemma finiteG_ae [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    (hl : ∀ k, P.map (g k) = expMeasure 1) (hi : iIndepFun g P) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∃ K, t < psumG g K ω := by
  rw [ae_iff]
  have hb : ∀ m, (P {ω | ¬ ∃ K, t < psumG g K ω}).toReal ≤ 1 - surv 1 m t := by
    intro m
    have hsub : {ω | ¬ ∃ K, t < psumG g K ω} ⊆ {ω | t < psumG g m ω}ᶜ := by
      intro ω hω h; exact hω ⟨m, h⟩
    have hms : MeasurableSet {ω | t < psumG g m ω} :=
      measurableSet_lt measurable_const (psumG_meas hm m)
    calc (P {ω | ¬ ∃ K, t < psumG g K ω}).toReal ≤ (P {ω | t < psumG g m ω}ᶜ).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
      _ = 1 - surv 1 m t := by
          rw [prob_compl_eq_one_sub hms, psumG_surv hm hl hi,
            ENNReal.toReal_sub_of_le (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (surv_le_one one_pos m t)) ENNReal.one_ne_top,
            ENNReal.toReal_ofReal (surv_nonneg one_pos m t)]
          simp
  have hlim : Tendsto (fun m => 1 - surv (1:ℝ) m t) atTop (𝓝 0) := by
    have := (surv_tendsto (r := 1) ht).const_sub 1
    simpa using this
  have h0 := ge_of_tendsto' hlim hb
  have h1 : (P {ω | ¬ ∃ K, t < psumG g K ω}).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
  rwa [ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at h1

/-- the event `{psum n ≤ t < psum (n+1)}` as a difference of measurable sets -/
lemma diffG_prob [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    (hl : ∀ k, P.map (g k) = expMeasure 1) (hi : iIndepFun g P) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    P ({ω | t < psumG g (n + 1) ω} \ {ω | t < psumG g n ω}) =
      ENNReal.ofReal (Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ)) := by
  set A := {ω | t < psumG g (n + 1) ω}
  set C := {ω | t < psumG g n ω}
  have hC : MeasurableSet C := measurableSet_lt measurable_const (psumG_meas hm _)
  have e2 : P (A ∩ C) = P C := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [gapG_nonneg_ae hm hl] with ω hω
    simp only [A, C, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨lt_of_lt_of_le h (psumG_mono hω (Nat.le_succ n)), h⟩
  have e3 := measure_inter_add_diff (μ := P) A hC
  rw [e2] at e3
  have e4 : P (A \ C) = P A - P C := by
    rw [← e3, ENNReal.add_sub_cancel_left (measure_ne_top _ _)]
  rw [e4, psumG_surv hm hl hi, psumG_surv hm hl hi,
    ← ENNReal.ofReal_sub _ (surv_nonneg one_pos _ _)]
  congr 1
  rw [surv, surv, if_neg (not_lt.2 ht), if_neg (not_lt.2 ht), Finset.sum_range_succ]
  simp only [one_mul]
  ring

lemma cntG_ae [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    (hl : ∀ k, P.map (g k) = expMeasure 1) (hi : iIndepFun g P) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ n, (cntG g t ω = n ↔
      ω ∈ ({ω | t < psumG g (n + 1) ω} \ {ω | t < psumG g n ω})) := by
  filter_upwards [gapG_nonneg_ae hm hl, finiteG_ae hm hl hi ht] with ω hω hK n
  rw [cntG_iff ht hω hK n]
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_lt]
  tauto

lemma cntG_poisson [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    (hl : ∀ k, P.map (g k) = expMeasure 1) (hi : iIndepFun g P) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    P {ω | cntG g t ω = n} =
      ENNReal.ofReal (Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ)) := by
  rw [← diffG_prob hm hl hi ht n]
  refine measure_congr (Filter.eventuallyEq_set.2 ?_)
  filter_upwards [cntG_ae hm hl hi ht] with ω hω
  exact hω n

lemma hasSum_poisson_mean {t : ℝ} :
    HasSum (fun n : ℕ => (n : ℝ) * (Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ))) t := by
  have h := NormedSpace.expSeries_div_hasSum_exp t
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-t) * t)
  have e : Real.exp (-t) * t * Real.exp t = t := by
    rw [mul_comm (Real.exp (-t)) t, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      mul_one]
  rw [e] at h2
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_mul, sub_zero]
  refine h2.congr_fun (fun k => ?_)
  push_cast
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

lemma cntG_mean [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    (hl : ∀ k, P.map (g k) = expMeasure 1) (hi : iIndepFun g P) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (cntG g t ω : ENNReal) ∂P = ENNReal.ofReal t := by
  set D : ℕ → Set Ω := fun n => {ω | t < psumG g (n + 1) ω} \ {ω | t < psumG g n ω}
  have hD : ∀ n, MeasurableSet (D n) := fun n =>
    (measurableSet_lt measurable_const (psumG_meas hm _)).diff
      (measurableSet_lt measurable_const (psumG_meas hm _))
  have hae : ∀ᵐ ω ∂P, (cntG g t ω : ENNReal) =
      ∑' n : ℕ, (n : ENNReal) * (D n).indicator 1 ω := by
    filter_upwards [cntG_ae hm hl hi ht] with ω hω
    have : ∀ n : ℕ, (n : ENNReal) * (D n).indicator 1 ω =
        if n = cntG g t ω then (cntG g t ω : ENNReal) else 0 := by
      intro n
      by_cases hn : n = cntG g t ω
      · have : ω ∈ D n := (hω n).1 hn.symm
        rw [if_pos hn, Set.indicator_of_mem this, hn]; simp
      · have : ω ∉ D n := fun h => hn ((hω n).2 h).symm
        rw [if_neg hn, Set.indicator_of_notMem this]; simp
    simp_rw [this]
    rw [tsum_ite_eq]
  rw [lintegral_congr_ae hae, lintegral_tsum (fun n =>
    ((measurable_one.indicator (hD n)).const_mul (n : ENNReal)).aemeasurable)]
  have hterm : ∀ n : ℕ, ∫⁻ ω, (n : ENNReal) * (D n).indicator 1 ω ∂P =
      ENNReal.ofReal ((n : ℝ) * (Real.exp (-t) * t ^ n / (Nat.factorial n : ℝ))) := by
    intro n
    rw [lintegral_const_mul _ (measurable_one.indicator (hD n)), lintegral_indicator_one (hD n),
      diffG_prob hm hl hi ht n, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hasSum_poisson_mean.summable,
    hasSum_poisson_mean.tsum_eq]

end Gen

section DCM
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Type*} [MeasurableSpace E]

lemma RS_gap_law [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) (k : ℕ) :
    P.map (S.gap k) = expMeasure 1 := by
  haveI := S.markLaw_isProb
  have h := S.pair_law k
  have hpair : Measurable (fun ω => (S.gap k ω, S.mark k ω)) :=
    (S.gap_measurable k).prodMk (S.mark_measurable k)
  have : S.gap k = Prod.fst ∘ (fun ω => (S.gap k ω, S.mark k ω)) := rfl
  rw [this, ← Measure.map_map measurable_fst hpair, h, Measure.map_fst_prod]
  simp

lemma RS_gap_indep (S : ResupplySystem Ω P E) : iIndepFun S.gap P := by
  have := S.pair_indep.comp (fun _ p => p.1) (fun _ => measurable_fst)
  exact this

lemma demandCount_eq (S : ResupplySystem Ω P E) (t : ℝ) (ω : Ω) :
    S.demandCount t ω = cntG S.gap (S.meanFn t) ω := rfl

lemma meanFn_nonneg (S : ResupplySystem Ω P E) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ S.meanFn t :=
  intervalIntegral.integral_nonneg ht (fun s _ => S.rate_nonneg s)

theorem demand_count_mean_core [IsProbabilityMeasure P] (S : ResupplySystem Ω P E)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (S.demandCount t ω : ENNReal) ∂P = ENNReal.ofReal (∫ s in (0 : ℝ)..t, S.rate s) := by
  simp_rw [demandCount_eq]
  exact cntG_mean S.gap_measurable (RS_gap_law S) (RS_gap_indep S) (meanFn_nonneg S ht)

end DCM

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

section OSG
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem osG_succ [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    {r : ℝ} (hr : 0 < r) (hl : ∀ k, P.map (g k) = expMeasure r) (hi : iIndepFun g P)
    {t : ℝ} (ht : 0 < t)
    (hnn : ∀ᵐ ω ∂P, ∀ k, 0 ≤ g k ω) (hfin : ∀ᵐ ω ∂P, ∃ K, t < psumG g K ω) (m : ℕ)
    {A : Set (Fin (m + 1) → ℝ)} (hA : MeasurableSet A) :
    P ({ω | cntG g t ω = m + 1} ∩ {ω | (fun i : Fin (m + 1) => psumG g (i + 1) ω) ∈ A}) =
      ENNReal.ofReal (r ^ (m + 1) * Real.exp (-(r * t))) *
        volume (A ∩ {x : Fin (m + 1) → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t}) := by
  set O := {x : Fin (m + 1) → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t} with hO
  let gv : Ω → (Fin (m + 1) → ℝ) := fun ω i => g i ω
  have hgv : Measurable gv := measurable_pi_lambda _ (fun i => hm i)
  have harr : ∀ ω, (fun i : Fin (m + 1) => psumG g (i + 1) ω) = Lmap (m + 1) (gv ω) := by
    intro ω; funext i
    rw [Lmap_apply]
    simp only [psumG]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range] at hk
    simp only [extv, dif_pos (show k < m + 1 by omega), gv]
  have hps : ∀ ω, psumG g (m + 1) ω = ∑ i, gv ω i := by
    intro ω
    simp only [psumG, gv]
    exact (Fin.sum_univ_eq_sum_range (fun k => g k ω) (m + 1)).symm
  have hI : iIndepFun (fun (i : Fin (m + 1)) ω => g i ω) P :=
    hi.precomp (g := fun i : Fin (m + 1) => i.val) Fin.val_injective
  have hlaw : P.map gv = Measure.pi (fun _ : Fin (m + 1) => expMeasure r) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (f := fun (i : Fin (m + 1)) ω => g i ω)
      (fun i : Fin (m + 1) => (hm i).aemeasurable)).1 hI]
    congr 1; funext i; exact hl i
  have hind : IndepFun gv (g (m + 1)) P := by
    have hd : Disjoint (Finset.range (m + 1)) ({m + 1} : Finset ℕ) := by
      rw [Finset.disjoint_singleton_right]; simp
    have h1 := hi.indepFun_finset _ _ hd hm
    have hmem : ∀ i : Fin (m + 1), i.val ∈ Finset.range (m + 1) := by
      intro i; exact Finset.mem_range.2 i.isLt
    have hφ : Measurable (fun v : (Finset.range (m + 1)) → ℝ =>
        fun i : Fin (m + 1) => v ⟨i.val, hmem i⟩) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    have hψ : Measurable (fun v : ({m + 1} : Finset ℕ) → ℝ =>
        v ⟨m + 1, Finset.mem_singleton_self _⟩) := measurable_pi_apply _
    exact h1.comp hφ hψ
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
  have e1 : P ({ω | cntG g t ω = m + 1} ∩
      {ω | (fun i : Fin (m + 1) => psumG g (i + 1) ω) ∈ A}) =
      P ((fun ω => (gv ω, g (m + 1) ω)) ⁻¹' W) := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hnn, hfin] with ω hω hK
    show (cntG g t ω = m + 1 ∧ (fun i : Fin (m + 1) => psumG g (i + 1) ω) ∈ A) ↔
      (Lmap (m + 1) (gv ω) ∈ A ∧ ∑ i, gv ω i ≤ t ∧ t < ∑ i, gv ω i + g (m + 1) ω)
    rw [cntG_iff ht.le hω hK, harr, ← hps]
    have : psumG g (m + 1 + 1) ω = psumG g (m + 1) ω + g (m + 1) ω := by
      simp [psumG, Finset.sum_range_succ]
    rw [this]
    tauto
  rw [e1, ← Measure.map_apply (hgv.prodMk (hm _)) hW,
    (indepFun_iff_map_prod_eq_prod_map_map hgv.aemeasurable
      (hm _).aemeasurable).1 hind, Measure.prod_apply hW, hlaw, hl,
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

theorem osG_core [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} (hm : ∀ k, Measurable (g k))
    (hl : ∀ k, P.map (g k) = expMeasure 1) (hi : iIndepFun g P) {t : ℝ} (ht : 0 < t)
    (n : ℕ) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    P ({ω | cntG g t ω = n} ∩ {ω | (fun i : Fin n => psumG g (i + 1) ω) ∈ A}) =
      P {ω | cntG g t ω = n} *
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
    rw [osG_succ hm one_pos hl hi ht (gapG_nonneg_ae hm hl) (finiteG_ae hm hl hi ht.le) m hA,
      cntG_poisson hm hl hi ht.le, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg
        (Real.exp_pos _).le (pow_nonneg ht.le _)) (Nat.cast_nonneg _))]
    congr 2
    have : (t : ℝ) ^ (m + 1) ≠ 0 := by positivity
    have : ((m + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring

end OSG

section Sym

lemma sortset_eq {n : ℕ} (A : Set (Fin n → ℝ)) :
    {x : Fin n → ℝ | x ∘ Tuple.sort x ∈ A} = ⋃ σ : Equiv.Perm (Fin n),
      ({x | Monotone (x ∘ σ) ∧ ∀ i j, i < j → x (σ i) = x (σ j) → σ i < σ j} ∩
        {x | x ∘ σ ∈ A}) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro h; exact ⟨Tuple.sort x, Tuple.eq_sort_iff.1 rfl, h⟩
  · rintro ⟨σ, h1, h2⟩
    rwa [Tuple.eq_sort_iff.2 h1] at h2

lemma sortset_meas {n : ℕ} {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    MeasurableSet {x : Fin n → ℝ | x ∘ Tuple.sort x ∈ A} := by
  rw [sortset_eq]
  refine MeasurableSet.iUnion (fun σ => MeasurableSet.inter ?_ ?_)
  · have h1 : ∀ i j : Fin n, Measurable (fun x : Fin n → ℝ => x (σ i) ≤ x (σ j)) := fun i j =>
      measurableSet_setOf.1 (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
    have h2 : ∀ i j : Fin n, Measurable (fun x : Fin n → ℝ => x (σ i) = x (σ j)) := fun i j =>
      measurableSet_setOf.1 (measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _))
    refine measurableSet_setOf.2 (Measurable.and ?_ ?_)
    · have : (fun x : Fin n → ℝ => Monotone (x ∘ σ)) =
          fun x => ∀ i j : Fin n, i ≤ j → x (σ i) ≤ x (σ j) := by
        funext x; rfl
      rw [this]
      exact Measurable.forall (fun i => Measurable.forall (fun j =>
        Measurable.imp measurable_const (h1 i j)))
    · exact Measurable.forall (fun i => Measurable.forall (fun j =>
        Measurable.imp measurable_const (Measurable.imp (h2 i j) measurable_const)))
  · exact (measurable_pi_lambda _ (fun i => measurable_pi_apply _)) hA

lemma vol_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) :
    volume {y : Fin n → ℝ | y ∘ σ ∈ S} = volume S := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) σ.symm
  have e : {y : Fin n → ℝ | y ∘ σ ∈ S} =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm) ⁻¹' S := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have : y ∘ σ = MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ.symm y := by
      funext i
      have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) σ.symm y (σ i)
      simp only [Equiv.symm_apply_apply] at this
      rw [Function.comp_apply, ← this]
    rw [this]
  rw [e, h.measure_preimage hS.nullMeasurableSet]

lemma diag_null {n : ℕ} : volume {y : Fin n → ℝ | ¬ Function.Injective y} = 0 := by
  have hsub : {y : Fin n → ℝ | ¬ Function.Injective y} ⊆
      ⋃ i : Fin n, ⋃ j : Fin n, {y | i ≠ j ∧ y i = y j} := by
    intro y hy
    simp only [Function.Injective, not_forall, Set.mem_setOf_eq] at hy
    obtain ⟨i, j, h1, h2⟩ := hy
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨i, j, h2, h1⟩
  refine measure_mono_null hsub (measure_iUnion_null (fun i => measure_iUnion_null (fun j => ?_)))
  by_cases hij : i = j
  · simp [hij]
  · refine measure_mono_null (fun y hy => hy.2) ?_
    have := hyperplane_null (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i -
      LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j) 0 (Pi.single i 1)
      (by simp [Pi.single_apply, Ne.symm hij])
    refine measure_mono_null (fun y hy => ?_) this
    simp only [Set.mem_setOf_eq, LinearMap.sub_apply, LinearMap.coe_proj,
      Function.eval] at hy ⊢
    rw [hy, sub_self]

lemma vol_sort {n : ℕ} {c : ℝ} {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    volume ({y : Fin n → ℝ | y ∘ Tuple.sort y ∈ B} ∩ Set.univ.pi (fun _ => Set.Ioo 0 c)) =
      (Nat.factorial n : ENNReal) *
        volume (B ∩ {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < c}) := by
  set O := {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < c} with hO
  have hOm : MeasurableSet O := by
    have : O = {x : Fin n → ℝ | Monotone x ∧ Function.Injective x} ∩
        ⋂ i, {x | 0 < x i ∧ x i < c} := by
      ext x
      simp only [O, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1.monotone, h1.injective⟩, h2⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1.strictMono_of_injective h2, h3⟩
    rw [this]
    refine MeasurableSet.inter ?_ (MeasurableSet.iInter (fun i =>
      (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
        (measurableSet_lt (measurable_pi_apply i) measurable_const)))
    have h1 : ∀ i j : Fin n, Measurable (fun x : Fin n → ℝ => x i ≤ x j) := fun i j =>
      measurableSet_setOf.1 (measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _))
    have h2 : ∀ i j : Fin n, Measurable (fun x : Fin n → ℝ => x i = x j) := fun i j =>
      measurableSet_setOf.1 (measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _))
    refine measurableSet_setOf.2 (Measurable.and ?_ ?_)
    · show Measurable (fun x : Fin n → ℝ => ∀ i j : Fin n, i ≤ j → x i ≤ x j)
      exact Measurable.forall (fun i => Measurable.forall (fun j =>
        Measurable.imp measurable_const (h1 i j)))
    · show Measurable (fun x : Fin n → ℝ => ∀ i j : Fin n, x i = x j → i = j)
      exact Measurable.forall (fun i => Measurable.forall (fun j =>
        Measurable.imp (h2 i j) measurable_const))
  set E : Equiv.Perm (Fin n) → Set (Fin n → ℝ) := fun σ => {y | y ∘ σ ∈ B ∩ O} with hE
  have hEm : ∀ σ, MeasurableSet (E σ) := fun σ =>
    (measurable_pi_lambda _ (fun i => measurable_pi_apply _)) (hB.inter hOm)
  have hsm : ∀ {y : Fin n → ℝ} {σ : Equiv.Perm (Fin n)}, StrictMono (y ∘ σ) →
      σ = Tuple.sort y := by
    intro y σ h
    exact Tuple.eq_sort_iff.2 ⟨h.monotone, fun i j hij hf => absurd hf (h.lt_iff_lt.2 hij).ne⟩
  have hdisj : Pairwise (fun σ τ => Disjoint (E σ) (E τ)) := by
    intro σ τ hne
    rw [Set.disjoint_left]
    intro y h1 h2
    exact hne ((hsm h1.2.1).trans (hsm h2.2.1).symm)
  have hsub1 : (⋃ σ, E σ) ⊆
      {y : Fin n → ℝ | y ∘ Tuple.sort y ∈ B} ∩ Set.univ.pi (fun _ => Set.Ioo 0 c) := by
    intro y hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨σ, hyB, hyO, hyc⟩ := hy
    refine ⟨?_, ?_⟩
    · show y ∘ Tuple.sort y ∈ B
      rwa [← hsm hyO]
    · intro i _
      have := hyc (σ.symm i)
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
      exact this
  have hsub2 : {y : Fin n → ℝ | y ∘ Tuple.sort y ∈ B} ∩ Set.univ.pi (fun _ => Set.Ioo 0 c) ⊆
      (⋃ σ, E σ) ∪ {y : Fin n → ℝ | ¬ Function.Injective y} := by
    rintro y ⟨hyB, hyc⟩
    by_cases hinj : Function.Injective y
    · left
      simp only [Set.mem_iUnion]
      refine ⟨Tuple.sort y, hyB, ?_, fun i => hyc _ (Set.mem_univ _)⟩
      exact (Tuple.monotone_sort y).strictMono_of_injective
        (hinj.comp (Tuple.sort y).injective)
    · exact Or.inr hinj
  have hU : volume (⋃ σ, E σ) = (Nat.factorial n : ENNReal) * volume (B ∩ O) := by
    rw [measure_iUnion hdisj hEm, tsum_fintype]
    simp_rw [hE, vol_perm _ (hB.inter hOm)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  apply le_antisymm
  · calc _ ≤ volume ((⋃ σ, E σ) ∪ {y : Fin n → ℝ | ¬ Function.Injective y}) := measure_mono hsub2
      _ ≤ volume (⋃ σ, E σ) + volume {y : Fin n → ℝ | ¬ Function.Injective y} :=
          measure_union_le _ _
      _ = _ := by rw [diag_null, add_zero, hU]
  · rw [← hU]; exact measure_mono hsub1

/-- uniform law on `(0, c)` -/
noncomputable def unifM (c : ℝ) : Measure ℝ := ENNReal.ofReal (1 / c) • volume.restrict (Set.Ioo 0 c)

instance (c : ℝ) : IsFiniteMeasure (unifM c) := by
  refine ⟨?_⟩
  simp only [unifM, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioo, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

lemma pi_unif {n : ℕ} {c : ℝ} :
    Measure.pi (fun _ : Fin n => unifM c) =
      (ENNReal.ofReal (1 / c)) ^ n • volume.restrict (Set.univ.pi (fun _ : Fin n => Set.Ioo 0 c)) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.smul_apply, Measure.restrict_apply (MeasurableSet.univ_pi hs),
    ← Set.pi_inter_distrib, volume_pi_pi]
  simp only [unifM, Measure.smul_apply, Measure.restrict_apply (hs _), smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma unif_sort {n : ℕ} {c : ℝ} (hc : 0 < c) {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) :
    Measure.pi (fun _ : Fin n => unifM c) {y | y ∘ Tuple.sort y ∈ B} =
      ENNReal.ofReal ((Nat.factorial n : ℝ) / c ^ n) *
        volume (B ∩ {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < c}) := by
  rw [pi_unif, Measure.smul_apply, Measure.restrict_apply (sortset_meas hB), vol_sort hB,
    smul_eq_mul, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [one_div, inv_pow, div_eq_mul_inv, mul_comm]

lemma map_sort {n : ℕ} {ν μ : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure μ] {ψ : ℝ → ℝ}
    (hψ : Monotone ψ) (hμ : ν.map ψ = μ) {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    Measure.pi (fun _ : Fin n => μ) {x | x ∘ Tuple.sort x ∈ A} =
      Measure.pi (fun _ : Fin n => ν) {y | y ∘ Tuple.sort y ∈ (fun z i => ψ (z i)) ⁻¹' A} := by
  subst hμ
  rw [← Measure.pi_map_pi (fun _ => hψ.measurable.aemeasurable),
    Measure.map_apply (f := fun (x : Fin n → ℝ) (i : Fin n) => ψ (x i))
      (measurable_pi_lambda _ (fun i => hψ.measurable.comp (measurable_pi_apply i)))
      (sortset_meas hA)]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have : (fun i => ψ (y i)) ∘ Tuple.sort y = (fun i => ψ (y i)) ∘ Tuple.sort (fun i => ψ (y i)) :=
    Tuple.comp_sort_eq_comp_iff_monotone.2 (hψ.comp (Tuple.monotone_sort y))
  rw [← this]
  rfl

end Sym

section NP
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : Type*} [MeasurableSpace E]

lemma RS_meanFn_cont (S : ResupplySystem Ω P E) : Continuous S.meanFn := by
  have : S.meanFn = fun b => ∫ s in (0:ℝ)..b, S.rate s := rfl
  rw [this]
  exact intervalIntegral.continuous_primitive (fun a b =>
    (S.rate_intervalIntegrable a).symm.trans (S.rate_intervalIntegrable b)) 0

lemma RS_meanFn_mono (S : ResupplySystem Ω P E) {x y : ℝ} (hxy : x ≤ y) :
    S.meanFn x ≤ S.meanFn y := by
  unfold ResupplySystem.meanFn
  rw [← intervalIntegral.integral_add_adjacent_intervals (S.rate_intervalIntegrable x)
    ((S.rate_intervalIntegrable x).symm.trans (S.rate_intervalIntegrable y))]
  have := intervalIntegral.integral_nonneg (μ := volume) hxy (fun s _ => S.rate_nonneg s)
  linarith

lemma RS_meanFn_nonpos (S : ResupplySystem Ω P E) {t : ℝ} (ht : t ≤ 0) : S.meanFn t ≤ 0 := by
  unfold ResupplySystem.meanFn
  rw [intervalIntegral.integral_symm]
  have := intervalIntegral.integral_nonneg (μ := volume) ht (fun s _ => S.rate_nonneg s)
  linarith

lemma RS_meanFn_zero (S : ResupplySystem Ω P E) : S.meanFn 0 = 0 := by
  simp [ResupplySystem.meanFn]

noncomputable def phiS (S : ResupplySystem Ω P E) (γ : ℝ) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ γ ≤ S.meanFn s}

lemma phiS_mem (S : ResupplySystem Ω P E) {t γ : ℝ} (ht : 0 ≤ t) (hγ : γ ≤ S.meanFn t) :
    0 ≤ phiS S γ ∧ γ ≤ S.meanFn (phiS S γ) := by
  have hne : ({s : ℝ | 0 ≤ s ∧ γ ≤ S.meanFn s}).Nonempty := ⟨t, ht, hγ⟩
  have hbdd : BddBelow {s : ℝ | 0 ≤ s ∧ γ ≤ S.meanFn s} := ⟨0, fun s hs => hs.1⟩
  have hcl : IsClosed {s : ℝ | 0 ≤ s ∧ γ ≤ S.meanFn s} :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const (RS_meanFn_cont S))
  exact hcl.csInf_mem hne hbdd

lemma phiS_le (S : ResupplySystem Ω P E) {γ x : ℝ} (hx : 0 ≤ x) (h : γ ≤ S.meanFn x) :
    phiS S γ ≤ x :=
  csInf_le ⟨0, fun s hs => hs.1⟩ ⟨hx, h⟩

lemma phiS_le_iff (S : ResupplySystem Ω P E) {t γ x : ℝ} (ht : 0 ≤ t) (hγ : γ ≤ S.meanFn t)
    (hx : 0 ≤ x) : phiS S γ ≤ x ↔ γ ≤ S.meanFn x := by
  constructor
  · intro h
    have := phiS_mem S ht hγ
    exact this.2.trans (RS_meanFn_mono S h)
  · exact phiS_le S hx

noncomputable def psiS (S : ResupplySystem Ω P E) (t γ : ℝ) : ℝ :=
  phiS S (min γ (S.meanFn t))

lemma psiS_mono (S : ResupplySystem Ω P E) {t : ℝ} (ht : 0 ≤ t) : Monotone (psiS S t) := by
  intro a b hab
  unfold psiS
  have hb := phiS_mem S ht (min_le_right b (S.meanFn t))
  exact phiS_le S hb.1 ((min_le_min_right _ hab).trans hb.2)

lemma psiS_nonneg (S : ResupplySystem Ω P E) {t : ℝ} (ht : 0 ≤ t) (γ : ℝ) : 0 ≤ psiS S t γ :=
  (phiS_mem S ht (min_le_right γ (S.meanFn t))).1

lemma map_psi (S : ResupplySystem Ω P E) {t : ℝ} (hm : 0 < S.meanFn t)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ (Set.Iic x) = ENNReal.ofReal (S.arrivalCdf t x)) :
    (unifM (S.meanFn t)).map (psiS S t) = μ := by
  have ht : 0 < t := by
    by_contra h; push_neg at h; linarith [RS_meanFn_nonpos S h]
  set c := S.meanFn t with hc
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply (psiS_mono S ht.le).measurable measurableSet_Iic, hμ x]
  simp only [unifM, Measure.smul_apply, Measure.restrict_apply
    ((psiS_mono S ht.le).measurable measurableSet_Iic), smul_eq_mul]
  rcases lt_or_ge x 0 with hx | hx
  · have : psiS S t ⁻¹' Set.Iic x ∩ Set.Ioo 0 c = ∅ := by
      ext γ
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h; linarith [psiS_nonneg S ht.le γ]
    rw [this, ResupplySystem.arrivalCdf, if_pos hx]
    simp
  have hset : psiS S t ⁻¹' Set.Iic x ∩ Set.Ioo 0 c = Set.Ioo 0 c ∩ Set.Iic (S.meanFn x) := by
    ext γ
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      unfold psiS at h1
      rw [min_eq_left h2.2.le] at h1
      exact (phiS_le_iff S ht.le h2.2.le hx).1 h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      unfold psiS
      rw [min_eq_left h2.2.le]
      exact (phiS_le_iff S ht.le h2.2.le hx).2 h1
  rw [hset]
  have hmx0 : 0 ≤ S.meanFn x := by
    have := RS_meanFn_mono S hx; rwa [RS_meanFn_zero] at this
  rcases le_or_gt c (S.meanFn x) with hcx | hcx
  · have : Set.Ioo 0 c ∩ Set.Iic (S.meanFn x) = Set.Ioo 0 c := by
      ext γ; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic]
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, by linarith [h.2]⟩
    rw [this, Real.volume_Ioo, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hval : S.arrivalCdf t x = 1 := by
      rw [ResupplySystem.arrivalCdf, if_neg (not_lt.2 hx)]
      split_ifs with hxt
      · have : S.meanFn x ≤ c := RS_meanFn_mono S hxt.le
        rw [show S.meanFn x = c by linarith, div_self hm.ne']
      · rfl
    rw [hval, sub_zero, one_div, inv_mul_cancel₀ hm.ne']
  · have : Set.Ioo 0 c ∩ Set.Iic (S.meanFn x) = Set.Ioc 0 (S.meanFn x) := by
      ext γ; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · intro h; exact ⟨h.1.1, h.2⟩
      · intro h; exact ⟨⟨h.1, by linarith [h.2]⟩, h.2⟩
    have hxt : x < t := by
      by_contra h; push_neg at h; linarith [RS_meanFn_mono S h]
    rw [this, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity), ResupplySystem.arrivalCdf,
      if_neg (not_lt.2 hx), if_pos hxt]
    congr 1
    rw [sub_zero, ← hc]; ring

theorem arrival_os_np [IsProbabilityMeasure P] (S : ResupplySystem Ω P E)
    {t : ℝ} (hm : 0 < S.meanFn t) (n : ℕ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ (Set.Iic x) = ENNReal.ofReal (S.arrivalCdf t x))
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    P ({ω | S.demandCount t ω = n} ∩ {ω | (fun i : Fin n => S.epoch (i : ℕ) ω) ∈ A}) =
      P {ω | S.demandCount t ω = n} *
        Measure.pi (fun _ : Fin n => μ) {x : Fin n → ℝ | x ∘ Tuple.sort x ∈ A} := by
  have ht : 0 < t := by
    by_contra h; push_neg at h; linarith [RS_meanFn_nonpos S h]
  have hψm : Monotone (psiS S t) := psiS_mono S ht.le
  have hΨ : Measurable (fun (z : Fin n → ℝ) (i : Fin n) => psiS S t (z i)) :=
    measurable_pi_lambda _ (fun i => hψm.measurable.comp (measurable_pi_apply i))
  have hB : MeasurableSet ((fun (z : Fin n → ℝ) (i : Fin n) => psiS S t (z i)) ⁻¹' A) := hΨ hA
  have hgm := S.gap_measurable
  have hl := RS_gap_law S
  have hi := RS_gap_indep S
  have e1 : P ({ω | S.demandCount t ω = n} ∩ {ω | (fun i : Fin n => S.epoch (i : ℕ) ω) ∈ A}) =
      P ({ω | cntG S.gap (S.meanFn t) ω = n} ∩ {ω | (fun i : Fin n => psumG S.gap (i + 1) ω) ∈
        (fun (z : Fin n → ℝ) (i : Fin n) => psiS S t (z i)) ⁻¹' A}) := by
    refine measure_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [gapG_nonneg_ae hgm hl, finiteG_ae hgm hl hi hm.le] with ω hω hK
    have key : cntG S.gap (S.meanFn t) ω = n →
        (fun i : Fin n => psiS S t (psumG S.gap (i + 1) ω)) = fun i : Fin n => S.epoch (i : ℕ) ω := by
      intro h
      funext i
      have h2 := ((cntG_iff hm.le hω hK n).1 h).1
      have h3 : psumG S.gap (i + 1) ω ≤ S.meanFn t :=
        (psumG_mono hω (Nat.succ_le_of_lt i.isLt)).trans h2
      simp only [psiS, min_eq_left h3]
      rfl
    show (S.demandCount t ω = n ∧ (fun i : Fin n => S.epoch (i : ℕ) ω) ∈ A) ↔
      (cntG S.gap (S.meanFn t) ω = n ∧
        (fun i : Fin n => psiS S t (psumG S.gap (i + 1) ω)) ∈ A)
    rw [demandCount_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [key h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [key h1] at h2; exact h2⟩
  rw [e1, osG_core hgm hl hi hm n hB, map_sort hψm (map_psi S hm μ hμ) hA, unif_sort hm hB]
  rfl

end NP

end ServiceParts.NonstatPalm

open ServiceParts.NonstatPalm


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : ResupplySystem Ω P E)
    {t : ℝ} (hm : 0 < S.meanFn t) (n : ℕ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ x : ℝ, μ (Set.Iic x) = ENNReal.ofReal (S.arrivalCdf t x))
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    P ({ω | S.demandCount t ω = n} ∩ {ω | (fun i : Fin n => S.epoch (i : ℕ) ω) ∈ A}) =
      P {ω | S.demandCount t ω = n} *
        Measure.pi (fun _ : Fin n => μ) {x : Fin n → ℝ | x ∘ Tuple.sort x ∈ A} := by
  exact arrival_os_np S hm n μ hμ hA
