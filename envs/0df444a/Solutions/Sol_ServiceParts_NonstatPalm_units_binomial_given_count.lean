-- Prove2me | solution 1 for ServiceParts.NonstatPalm.units_binomial_given_count
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:53:10.320017+00:00
-- url     : https://prove2.me/submissions/a4dd193a-bebc-482b-9abb-a28498e21059

-- Count helpers reused from accepted submission 32be2b68-1bb8-4771-9ae8-4af42acb4ec1.
-- Inverse-time helpers reused from accepted submission 297117c6-888f-4ec2-bf9c-e4eeb746d3d5.
import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_ResupplySystem
import Theorems.Thm_ServiceParts_NonstatPalm_arrival_times_order_statistics

open MeasureTheory ProbabilityTheory
open scoped ENNReal
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

end ServiceParts.NonstatPalm


namespace ServiceParts.NonstatPalm
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

lemma np_cdf_bounds (S : ResupplySystem Ω P E) (s w : ℝ) :
    0 ≤ S.resupplyCdf s w ∧ S.resupplyCdf s w ≤ 1 := by
  haveI := S.markLaw_isProb
  exact ⟨ENNReal.toReal_nonneg, by
    simpa [ResupplySystem.resupplyCdf] using
      (ENNReal.toReal_mono ENNReal.one_ne_top
        (show S.markLaw {e | S.resupply s e ≤ w} ≤ 1 from prob_le_one))⟩

lemma np_survival_meas (S : ResupplySystem Ω P E) (t : ℝ) :
    Measurable (fun s => 1 - S.resupplyCdf s (t - s)) := by
  haveI := S.markLaw_isProb
  have h : MeasurableSet {z : ℝ × E | S.resupply z.1 z.2 ≤ t - z.1} :=
    measurableSet_le S.resupply_measurable (measurable_const.sub measurable_fst)
  exact measurable_const.sub (measurable_measure_prodMk_left h).ennreal_toReal

lemma np_alpha_integrable (S : ResupplySystem Ω P E) (t : ℝ) :
    IntervalIntegrable (fun s => (1 - S.resupplyCdf s (t - s)) * S.rate s) volume 0 t := by
  have hb : ∀ᵐ s ∂volume, ‖1 - S.resupplyCdf s (t - s)‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (np_cdf_bounds S s (t-s)).2)]
      linarith [(np_cdf_bounds S s (t-s)).1])
  constructor
  · exact (S.rate_intervalIntegrable t).1.bdd_mul
      (np_survival_meas S t).aestronglyMeasurable (ae_restrict_of_ae hb)
  · exact (S.rate_intervalIntegrable t).2.bdd_mul
      (np_survival_meas S t).aestronglyMeasurable (ae_restrict_of_ae hb)

lemma np_alpha_bounds (S : ResupplySystem Ω P E) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ S.alpha t ∧ S.alpha t ≤ S.meanFn t := by
  constructor
  · exact intervalIntegral.integral_nonneg ht (fun s _ =>
      mul_nonneg (sub_nonneg.2 (np_cdf_bounds S s (t-s)).2) (S.rate_nonneg s))
  · exact intervalIntegral.integral_mono ht (np_alpha_integrable S t)
      (S.rate_intervalIntegrable t) (fun s => by
        have := (np_cdf_bounds S s (t-s)).1
        nlinarith [S.rate_nonneg s])

noncomputable def np_cnt (S : ResupplySystem Ω P E) (t : ℝ) (n : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun i : Fin n =>
    t < psiS S t (S.unitPoint i ω) + S.resupply (psiS S t (S.unitPoint i ω)) (S.mark i ω))).card

lemma np_cnt_meas (S : ResupplySystem Ω P E) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Measurable (fun ω => (np_cnt S t n ω : ℝ)) := by
  classical
  unfold np_cnt
  simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  refine Finset.measurable_sum _ (fun i _ => Measurable.ite ?_ measurable_const measurable_const)
  have h := (psiS_mono S ht).measurable.comp (psumG_meas S.gap_measurable (i.val + 1))
  exact measurableSet_lt measurable_const (h.add
    (S.resupply_measurable.comp (h.prodMk (S.mark_measurable i))))

lemma np_units_eq (S : ResupplySystem Ω P E) {t : ℝ} {ω : Ω}
    (hω : ∀ k, 0 ≤ S.gap k ω) {n : ℕ}
    (h : psumG S.gap n ω ≤ S.meanFn t ∧ S.meanFn t < psumG S.gap (n+1) ω) :
    S.unitsInResupply t ω = np_cnt S t n ω := by
  classical
  have hepoch : ∀ i : Fin n,
      psiS S t (S.unitPoint i ω) = S.epoch i ω := by
    intro i
    have hi := (psumG_mono hω (Nat.succ_le_of_lt i.isLt)).trans h.1
    simp only [psiS, show S.unitPoint i ω = psumG S.gap (i.val + 1) ω from rfl,
      min_eq_left hi]
    rfl
  have hset : {k : ℕ | S.unitPoint k ω ≤ S.meanFn t ∧ t < S.epoch k ω + S.resupplyTime k ω} =
      ↑((Finset.range n).filter (fun k => t < S.epoch k ω + S.resupplyTime k ω)) := by
    ext k
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hk; push_neg at hk
      have := psumG_mono hω (show n + 1 ≤ k + 1 by omega)
      change psumG S.gap (k + 1) ω ≤ S.meanFn t at h1
      linarith [h.2]
    · rintro ⟨hk, h2⟩
      refine ⟨?_, h2⟩
      exact (psumG_mono hω (show k+1 ≤ n by omega)).trans h.1
  unfold ResupplySystem.unitsInResupply np_cnt
  rw [hset, Set.ncard_coe_finset]
  simp_rw [hepoch]
  rw [Finset.card_filter, Finset.card_filter]
  exact (Fin.sum_univ_eq_sum_range
    (fun k => if t < S.epoch k ω + S.resupplyTime k ω then 1 else 0) n).symm

lemma np_joint_ae [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (ht : 0 ≤ t) (n k : ℕ) :
    ({ω | S.unitsInResupply t ω = k} ∩ {ω | S.demandCount t ω = n} : Set Ω) =ᵐ[P]
      ({ω | np_cnt S t n ω = k} ∩
        {ω | psumG S.gap n ω ≤ S.meanFn t ∧ S.meanFn t < psumG S.gap (n+1) ω} : Set Ω) := by
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [gapG_nonneg_ae S.gap_measurable (RS_gap_law S),
    finiteG_ae S.gap_measurable (RS_gap_law S) (RS_gap_indep S) (meanFn_nonneg S ht)] with ω hω hK
  change (S.unitsInResupply t ω = k ∧ cntG S.gap (S.meanFn t) ω = n) ↔
    (np_cnt S t n ω = k ∧ psumG S.gap n ω ≤ S.meanFn t ∧
      S.meanFn t < psumG S.gap (n+1) ω)
  rw [cntG_iff (meanFn_nonneg S ht) hω hK n]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(np_units_eq S hω h2) ▸ h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(np_units_eq S hω h2).symm ▸ h1, h2⟩

lemma np_joint_nullmeas [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (ht : 0 ≤ t) (n k : ℕ) :
    NullMeasurableSet ({ω | S.unitsInResupply t ω = k} ∩ {ω | S.demandCount t ω = n}) P := by
  refine NullMeasurableSet.congr ?_ (np_joint_ae S ht n k).symm
  refine MeasurableSet.nullMeasurableSet ?_
  have he : {ω | np_cnt S t n ω = k} = {ω | (np_cnt S t n ω : ℝ) = (k : ℝ)} := by
    ext ω; simp only [Set.mem_setOf_eq, Nat.cast_inj]
  rw [he]
  exact (measurableSet_eq_fun (np_cnt_meas S ht n) measurable_const).inter
    ((measurableSet_le (psumG_meas S.gap_measurable n) measurable_const).inter
      (measurableSet_lt measurable_const (psumG_meas S.gap_measurable (n+1))))

lemma np_count_real [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) :
    (P {ω | S.demandCount t ω = n}).toReal =
      Real.exp (-S.meanFn t) * S.meanFn t ^ n / (Nat.factorial n : ℝ) := by
  have hm0 := meanFn_nonneg S ht
  change (P {ω | cntG S.gap (S.meanFn t) ω = n}).toReal = _
  rw [cntG_poisson S.gap_measurable (RS_gap_law S) (RS_gap_indep S) (meanFn_nonneg S ht),
    ENNReal.toReal_ofReal (by positivity)]

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

lemma np_mark_law [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) (k : ℕ) :
    P.map (S.mark k) = S.markLaw := by
  haveI := S.markLaw_isProb
  haveI := isProbabilityMeasure_expMeasure (one_pos (α := ℝ))
  have hpair : Measurable (fun ω => (S.gap k ω, S.mark k ω)) :=
    (S.gap_measurable k).prodMk (S.mark_measurable k)
  have he : S.mark k = Prod.snd ∘ (fun ω => (S.gap k ω, S.mark k ω)) := rfl
  rw [he, ← Measure.map_map measurable_snd hpair, S.pair_law, Measure.map_snd_prod]
  simp

lemma np_mark_indep (S : ResupplySystem Ω P E) : iIndepFun S.mark P :=
  S.pair_indep.comp (fun _ => Prod.snd) (fun _ => measurable_snd)

lemma np_vectors_indep [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) (N : ℕ) :
    IndepFun (fun ω => fun i : Fin N => S.gap i ω)
      (fun ω => fun i : Fin N => S.mark i ω) P := by
  haveI := S.markLaw_isProb
  haveI := isProbabilityMeasure_expMeasure (one_pos (α := ℝ))
  let V : Ω → Fin N → ℝ × E := fun ω i => (S.gap i ω, S.mark i ω)
  have hVm : Measurable V := measurable_pi_lambda _ (fun i =>
    (S.gap_measurable i).prodMk (S.mark_measurable i))
  have hV : P.map V = Measure.pi (fun _ : Fin N => (expMeasure 1).prod S.markLaw) := by
    have hi := S.pair_indep.precomp (g := fun i : Fin N => (i:ℕ)) Fin.val_injective
    rw [iIndepFun.map_fun_eq_pi_map (fun i : Fin N =>
      ((S.gap_measurable i).prodMk (S.mark_measurable i)).aemeasurable) hi]
    simp_rw [S.pair_law]
  have hG : P.map (fun ω => fun i : Fin N => S.gap i ω) =
      Measure.pi (fun _ : Fin N => expMeasure 1) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i : Fin N => (S.gap_measurable i).aemeasurable)
      ((RS_gap_indep S).precomp Fin.val_injective)]
    simp_rw [RS_gap_law S]
  have hM : P.map (fun ω => fun i : Fin N => S.mark i ω) =
      Measure.pi (fun _ : Fin N => S.markLaw) := by
    rw [iIndepFun.map_fun_eq_pi_map (fun i : Fin N => (S.mark_measurable i).aemeasurable)
      ((np_mark_indep S).precomp Fin.val_injective)]
    simp_rw [np_mark_law S]
  refine (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pi_lambda _ (fun i : Fin N => S.gap_measurable i)).aemeasurable
    (measurable_pi_lambda _ (fun i : Fin N => S.mark_measurable i)).aemeasurable).2 ?_
  rw [hG, hM]
  have h := congrArg (Measure.map (MeasurableEquiv.arrowProdEquivProdArrow ℝ E (Fin N))) hV
  rw [Measure.map_map (MeasurableEquiv.measurable _) hVm,
    (measurePreserving_arrowProdEquivProdArrow ℝ E (Fin N)
      (fun _ => expMeasure 1) (fun _ => S.markLaw)).map_eq] at h
  exact h

noncomputable def np_tv (S : ResupplySystem Ω P E) (t : ℝ) (n : ℕ) (ω : Ω) : Fin n → ℝ :=
  fun i => psiS S t (S.unitPoint i ω)

lemma np_tv_meas (S : ResupplySystem Ω P E) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Measurable (np_tv S t n) :=
  measurable_pi_lambda _ (fun i =>
    (psiS_mono S ht).measurable.comp (psumG_meas S.gap_measurable (i.val+1)))

lemma np_joint_indep [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) :
    IndepFun (fun ω => (np_tv S t n ω, psumG S.gap n ω, psumG S.gap (n+1) ω))
      (fun ω => fun i : Fin n => S.mark i ω) P := by
  let get : (Fin (n+1) → ℝ) → ℕ → ℝ := fun v k => if hk : k < n+1 then v ⟨k,hk⟩ else 0
  have hget : ∀ k, Measurable (fun v => get v k) := by
    intro k
    by_cases hk : k < n+1
    · simpa only [get, dif_pos hk] using (measurable_pi_apply (⟨k,hk⟩ : Fin (n+1)))
    · simp only [get, dif_neg hk]; exact measurable_const
  let sumv : ℕ → (Fin (n+1) → ℝ) → ℝ := fun m v => ∑ k ∈ Finset.range m, get v k
  have hsum : ∀ m, Measurable (sumv m) := fun m =>
    Finset.measurable_sum _ (fun k _ => hget k)
  let φ : (Fin (n+1) → ℝ) → (Fin n → ℝ) × ℝ × ℝ := fun v =>
    ((fun i => psiS S t (sumv (i.val+1) v)), sumv n v, sumv (n+1) v)
  have hφ : Measurable φ := (measurable_pi_lambda _ (fun i : Fin n =>
    (psiS_mono S ht).measurable.comp (hsum (i.val+1)))).prodMk ((hsum n).prodMk (hsum (n+1)))
  let ψ : (Fin (n+1) → E) → (Fin n → E) := fun v i => v i.castSucc
  have hψ : Measurable ψ :=
    measurable_pi_lambda _ (fun i : Fin n => measurable_pi_apply i.castSucc)
  have h := (np_vectors_indep S (n+1)).comp hφ hψ
  have he : ∀ m ≤ n+1, ∀ ω, sumv m (fun i => S.gap i ω) = psumG S.gap m ω := by
    intro m hm ω
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k < n+1 := lt_of_lt_of_le (Finset.mem_range.1 hk) hm
    simp only [get, dif_pos hk']
  have hleft : (fun ω => φ (fun i : Fin (n+1) => S.gap i ω)) =
      fun ω => (np_tv S t n ω, psumG S.gap n ω, psumG S.gap (n+1) ω) := by
    funext ω
    simp only [φ]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      change psiS S t (sumv (i.val+1) (fun j : Fin (n+1) => S.gap j ω)) =
        psiS S t (psumG S.gap (i.val+1) ω)
      exact congrArg (psiS S t) (he (i.val+1) (by omega) ω)
    · exact he n (by omega) ω
    · exact he (n+1) le_rfl ω
  have hright : (fun ω => ψ (fun i : Fin (n+1) => S.mark i ω)) =
      (fun ω => fun i : Fin n => S.mark i ω) := rfl
  simp only [Function.comp_def] at h
  rw [hleft, hright] at h
  exact h

lemma np_marks_law [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) (n : ℕ) :
    P.map (fun ω => fun i : Fin n => S.mark i ω) = Measure.pi (fun _ => S.markLaw) := by
  rw [iIndepFun.map_fun_eq_pi_map (fun i : Fin n => (S.mark_measurable i).aemeasurable)
    ((np_mark_indep S).precomp Fin.val_injective)]
  simp_rw [np_mark_law S]

noncomputable def np_q (S : ResupplySystem Ω P E) (t s : ℝ) : ℝ≥0∞ :=
  S.markLaw {e | t < s + S.resupply s e}
noncomputable def np_r (S : ResupplySystem Ω P E) (t s : ℝ) : ℝ≥0∞ :=
  S.markLaw {e | s + S.resupply s e ≤ t}
noncomputable def np_F (S : ResupplySystem Ω P E) {n : ℕ} (t : ℝ) (k : ℕ)
    (s : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
    ∏ i, if i ∈ A then np_q S t (s i) else np_r S t (s i)

lemma np_q_meas (S : ResupplySystem Ω P E) (t : ℝ) : Measurable (np_q S t) := by
  haveI := S.markLaw_isProb
  exact measurable_measure_prodMk_left
    (measurableSet_lt measurable_const (measurable_fst.add S.resupply_measurable))
lemma np_r_meas (S : ResupplySystem Ω P E) (t : ℝ) : Measurable (np_r S t) := by
  haveI := S.markLaw_isProb
  exact measurable_measure_prodMk_left
    (measurableSet_le (measurable_fst.add S.resupply_measurable) measurable_const)
lemma np_F_meas (S : ResupplySystem Ω P E) {n : ℕ} (t : ℝ) (k : ℕ) :
    Measurable (np_F S t k (n := n)) := by
  classical
  unfold np_F
  refine Finset.measurable_sum _ (fun A _ => Finset.measurable_prod _ (fun i _ => ?_))
  by_cases hi : i ∈ A
  · simp only [hi, if_true]; exact (np_q_meas S t).comp (measurable_pi_apply i)
  · simp only [hi, if_false]; exact (np_r_meas S t).comp (measurable_pi_apply i)
lemma np_pi_count (S : ResupplySystem Ω P E) {n : ℕ} (t : ℝ) (k : ℕ)
    (s : Fin n → ℝ) :
    Measure.pi (fun _ : Fin n => S.markLaw)
      {l | (Finset.univ.filter (fun i => t < s i + S.resupply (s i) (l i))).card = k} =
      np_F S t k s := by
  classical
  haveI := S.markLaw_isProb
  have hset : {l : Fin n → E |
      (Finset.univ.filter (fun i => t < s i + S.resupply (s i) (l i))).card = k} =
      ⋃ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        Set.univ.pi (fun i => if i ∈ A then {e | t < s i + S.resupply (s i) e}
          else {e | s i + S.resupply (s i) e ≤ t}) := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, Set.mem_univ_pi, exists_prop]
    constructor
    · intro h
      refine ⟨_, h, fun i => ?_⟩
      split_ifs with hi
      · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] using hi
      · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Set.mem_setOf_eq] using hi
    · rintro ⟨A, hA, h⟩
      have : Finset.univ.filter (fun i => t < s i + S.resupply (s i) (l i)) = A := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := h i
        split_ifs at this with hi
        · exact ⟨fun _ => hi, fun _ => this⟩
        · exact ⟨fun h' => (not_lt_of_ge this h').elim, fun h' => (hi h').elim⟩
      rw [this, hA]
  rw [hset, measure_biUnion_finset]
  · unfold np_F
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
      simp only [hA, hB, if_true, if_false, Set.mem_setOf_eq] at a1 a2 <;>
      simp only [hA, hB] <;> linarith
  · intro A _
    refine MeasurableSet.univ_pi (fun i => ?_)
    have hm : Measurable (fun e => s i + S.resupply (s i) e) :=
      measurable_const.add (S.resupply_measurable.comp (measurable_const.prodMk measurable_id))
    split_ifs
    · exact measurableSet_lt measurable_const hm
    · exact measurableSet_le hm measurable_const

lemma np_F_perm (S : ResupplySystem Ω P E) {n : ℕ} (t : ℝ) (k : ℕ)
    (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) : np_F S t k (s ∘ σ) = np_F S t k s := by
  classical
  unfold np_F
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

lemma np_F_integral (S : ResupplySystem Ω P E) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {n : ℕ} (t : ℝ) (k : ℕ) :
    ∫⁻ s, np_F S t k s ∂(Measure.pi (fun _ : Fin n => μ)) =
      (n.choose k : ℝ≥0∞) * ((∫⁻ u, np_q S t u ∂μ) ^ k *
        (∫⁻ u, np_r S t u ∂μ) ^ (n-k)) := by
  classical
  unfold np_F
  have hf : ∀ A : Finset (Fin n), ∀ i,
      Measurable (fun u => if i ∈ A then np_q S t u else np_r S t u) := by
    intro A i
    by_cases hi : i ∈ A
    · simp only [hi, if_true]; exact np_q_meas S t
    · simp only [hi, if_false]; exact np_r_meas S t
  have hmeasA : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      Measurable (fun s : Fin n → ℝ => ∏ i, if i ∈ A then np_q S t (s i) else np_r S t (s i)) :=
    fun A _ => Finset.measurable_prod _ (fun i _ => (hf A i).comp (measurable_pi_apply i))
  rw [lintegral_finset_sum _ hmeasA]
  rw [Finset.sum_congr rfl (g := fun _ => (∫⁻ u, np_q S t u ∂μ) ^ k *
      (∫⁻ u, np_r S t u ∂μ) ^ (n-k))]
  · rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  · intro A hA
    rw [Finset.mem_powersetCard] at hA
    refine Eq.trans (lintegral_pi_prod (fun _ => μ)
      (fun i u => if i ∈ A then np_q S t u else np_r S t u) (hf A)) ?_
    have hc : ∀ i, (∫⁻ u, (if i ∈ A then np_q S t u else np_r S t u) ∂μ) =
        if i ∈ A then ∫⁻ u, np_q S t u ∂μ else ∫⁻ u, np_r S t u ∂μ := by
      intro i; split_ifs <;> rfl
    simp only [hc]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have h1 : (Finset.univ.filter (fun i => i ∈ A)).card = k := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]; exact hA.2
    have h2 : (Finset.univ.filter (fun i => ¬ i ∈ A)).card = n-k := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin n => i ∈ A)
      rw [h1, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [h1,h2]

noncomputable def np_arrivalMeasure (S : ResupplySystem Ω P E) (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / S.meanFn t) •
    (volume.restrict (Set.Ioc 0 t)).withDensity (fun s => ENNReal.ofReal (S.rate s))

lemma np_rate_lintegral (S : ResupplySystem Ω P E) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (S.rate s) = ENNReal.ofReal (S.meanFn t) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (S.rate_intervalIntegrable t).1
    (Filter.Eventually.of_forall S.rate_nonneg), ← intervalIntegral.integral_of_le ht]
  rfl

lemma np_arrival_Iic (S : ResupplySystem Ω P E) {t : ℝ} (hm : 0 < S.meanFn t) (x : ℝ) :
    np_arrivalMeasure S t (Set.Iic x) = ENNReal.ofReal (S.arrivalCdf t x) := by
  have ht : 0 < t := by
    by_contra h; push_neg at h; linarith [RS_meanFn_nonpos S h]
  unfold np_arrivalMeasure
  rw [Measure.smul_apply, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, smul_eq_mul]
  rcases lt_or_ge x 0 with hx | hx
  · have he : Set.Iic x ∩ Set.Ioc 0 t = ∅ := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hs hs0 _; linarith
    rw [he, Measure.restrict_empty]
    simp [ResupplySystem.arrivalCdf, hx]
  rcases lt_or_ge x t with hxt | hxt
  · have he : Set.Iic x ∩ Set.Ioc 0 t = Set.Ioc 0 x := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨hs,hs0,-⟩; exact ⟨hs0,hs⟩
      · rintro ⟨hs0,hs⟩; exact ⟨hs,hs0,hs.trans hxt.le⟩
    rw [he, np_rate_lintegral S hx, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [ResupplySystem.arrivalCdf, if_neg (not_lt.2 hx), if_pos hxt]
    ring
  · have he : Set.Iic x ∩ Set.Ioc 0 t = Set.Ioc 0 t := by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · exact fun h => h.2
      · intro h; exact ⟨h.2.trans hxt,h⟩
    rw [he, np_rate_lintegral S ht.le, ← ENNReal.ofReal_mul (by positivity)]
    simp [ResupplySystem.arrivalCdf, not_lt.2 hx, not_lt.2 hxt, hm.ne']

lemma np_arrival_prob (S : ResupplySystem Ω P E) {t : ℝ} (hm : 0 < S.meanFn t) :
    IsProbabilityMeasure (np_arrivalMeasure S t) := by
  have ht : 0 < t := by
    by_contra h; push_neg at h; linarith [RS_meanFn_nonpos S h]
  constructor
  rw [np_arrivalMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, smul_eq_mul, np_rate_lintegral S ht.le,
    ← ENNReal.ofReal_mul (by positivity)]
  simp [hm.ne']

lemma np_q_eq (S : ResupplySystem Ω P E) (t s : ℝ) :
    np_q S t s = ENNReal.ofReal (1 - S.resupplyCdf s (t-s)) := by
  haveI := S.markLaw_isProb
  have hmeas : MeasurableSet {e | S.resupply s e ≤ t-s} :=
    measurableSet_le (S.resupply_measurable.comp (measurable_const.prodMk measurable_id))
      measurable_const
  have he : {e | t < s + S.resupply s e} = {e | S.resupply s e ≤ t-s}ᶜ := by
    ext e; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
    constructor <;> intro h <;> linarith
  rw [np_q, he, measure_compl hmeas (measure_ne_top _ _), measure_univ,
    ResupplySystem.resupplyCdf, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
    ENNReal.ofReal_one, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma np_r_eq (S : ResupplySystem Ω P E) (t s : ℝ) :
    np_r S t s = ENNReal.ofReal (S.resupplyCdf s (t-s)) := by
  haveI := S.markLaw_isProb
  rw [np_r, ResupplySystem.resupplyCdf, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  congr 1
  ext e; simp only [Set.mem_setOf_eq]
  constructor <;> intro h <;> linarith

lemma np_q_integral (S : ResupplySystem Ω P E) {t : ℝ} (hm : 0 < S.meanFn t) :
    ∫⁻ s, np_q S t s ∂(np_arrivalMeasure S t) =
      ENNReal.ofReal (∫ s in (0:ℝ)..t, (1 - S.resupplyCdf s (t-s)) * (S.rate s / S.meanFn t)) := by
  have ht : 0 < t := by
    by_contra h; push_neg at h; linarith [RS_meanFn_nonpos S h]
  rw [np_arrivalMeasure, lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul₀
      (S.rate_intervalIntegrable t).1.aemeasurable.ennreal_ofReal (np_q_meas S t).aemeasurable]
  simp only [Pi.mul_apply, np_q_eq]
  simp_rw [← ENNReal.ofReal_mul (S.rate_nonneg _)]
  have hi : Integrable (fun s => S.rate s * (1-S.resupplyCdf s (t-s)))
      (volume.restrict (Set.Ioc 0 t)) := by
    change IntegrableOn (fun s => S.rate s * (1-S.resupplyCdf s (t-s))) (Set.Ioc 0 t) volume
    simpa only [mul_comm] using (np_alpha_integrable S t).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun s => mul_nonneg (S.rate_nonneg s)
      (sub_nonneg.2 (np_cdf_bounds S s (t-s)).2))),
    ← ENNReal.ofReal_mul (by positivity), ← intervalIntegral.integral_of_le ht.le]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  ring

lemma np_r_integral (S : ResupplySystem Ω P E) {t : ℝ} (hm : 0 < S.meanFn t) :
    ∫⁻ s, np_r S t s ∂(np_arrivalMeasure S t) =
      ENNReal.ofReal (1 - ∫ s in (0:ℝ)..t,
        (1 - S.resupplyCdf s (t-s)) * (S.rate s / S.meanFn t)) := by
  haveI := np_arrival_prob S hm
  haveI := S.markLaw_isProb
  have hqr : ∀ s, np_q S t s + np_r S t s = 1 := by
    intro s
    rw [np_q_eq, np_r_eq, ← ENNReal.ofReal_add
      (sub_nonneg.2 (np_cdf_bounds S s (t-s)).2) (np_cdf_bounds S s (t-s)).1]
    simp
  have hsum : (∫⁻ s, np_q S t s ∂(np_arrivalMeasure S t)) +
      (∫⁻ s, np_r S t s ∂(np_arrivalMeasure S t)) = 1 := by
    rw [← lintegral_add_left (np_q_meas S t), show (fun s => np_q S t s + np_r S t s) =
      (fun _ => 1) from funext hqr]
    simp
  have he : (∫⁻ s, np_r S t s ∂(np_arrivalMeasure S t)) =
      1 - ∫⁻ s, np_q S t s ∂(np_arrivalMeasure S t) := by
    rw [← hsum]
    exact (ENNReal.add_sub_cancel_left (by
      rw [np_q_integral S hm]; exact ENNReal.ofReal_ne_top)).symm
  rw [he, np_q_integral S hm, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (intervalIntegral.integral_nonneg
      (show 0 ≤ t by by_contra h; push_neg at h; linarith [RS_meanFn_nonpos S h.le])
      (fun s _ => mul_nonneg (sub_nonneg.2 (np_cdf_bounds S s (t-s)).2)
        (div_nonneg (S.rate_nonneg s) hm.le)))]
lemma np_E_eq_N [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (ht : 0 ≤ t) (n : ℕ) :
    ({ω | psumG S.gap n ω ≤ S.meanFn t ∧ S.meanFn t < psumG S.gap (n+1) ω} : Set Ω) =ᵐ[P]
      {ω | S.demandCount t ω = n} := by
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [gapG_nonneg_ae S.gap_measurable (RS_gap_law S),
    finiteG_ae S.gap_measurable (RS_gap_law S) (RS_gap_indep S) (meanFn_nonneg S ht)] with ω hω hK
  exact ((cntG_iff (meanFn_nonneg S ht) hω hK n).symm)

lemma np_tv_law [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (hm : 0 < S.meanFn t) (n : ℕ) :
    (P.restrict {ω | S.demandCount t ω = n}).map (np_tv S t n) =
      (P {ω | S.demandCount t ω = n}) •
        (Measure.pi (fun _ : Fin n => np_arrivalMeasure S t)).map (fun x => x ∘ Tuple.sort x) := by
  have ht : 0 < t := by
    by_contra h; push_neg at h; linarith [RS_meanFn_nonpos S h]
  haveI := np_arrival_prob S hm
  have hs : Measurable (fun x : Fin n → ℝ => x ∘ Tuple.sort x) := fun _ hA => sortset_meas hA
  ext A hA
  rw [Measure.map_apply (np_tv_meas S ht.le n) hA,
    Measure.restrict_apply ((np_tv_meas S ht.le n) hA), Measure.smul_apply,
    Measure.map_apply hs hA, smul_eq_mul, Set.inter_comm]
  have he : ({ω | S.demandCount t ω = n} ∩ np_tv S t n ⁻¹' A : Set Ω) =ᵐ[P]
      ({ω | S.demandCount t ω = n} ∩
        {ω | (fun i : Fin n => S.epoch i ω) ∈ A} : Set Ω) := by
    refine Filter.eventuallyEq_set.2 ?_
    filter_upwards [gapG_nonneg_ae S.gap_measurable (RS_gap_law S),
      finiteG_ae S.gap_measurable (RS_gap_law S) (RS_gap_indep S) hm.le] with ω hω hK
    change (S.demandCount t ω = n ∧ np_tv S t n ω ∈ A) ↔
      (S.demandCount t ω = n ∧ (fun i : Fin n => S.epoch i ω) ∈ A)
    by_cases hN : S.demandCount t ω = n
    · have hh := ((cntG_iff hm.le hω hK n).1 hN).1
      have hv : np_tv S t n ω = fun i : Fin n => S.epoch i ω := by
        funext i
        have hi : S.unitPoint i ω ≤ S.meanFn t :=
          (psumG_mono hω (Nat.succ_le_of_lt i.isLt)).trans hh
        simp only [np_tv, psiS, min_eq_left hi]
        rfl
      rw [hv]
    · simp only [hN, false_and]
  rw [measure_congr he]
  exact arrival_times_order_statistics S hm n (np_arrivalMeasure S t) (np_arrival_Iic S hm) hA

lemma np_joint_integral [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (ht : 0 ≤ t) (n k : ℕ) :
    P ({ω | S.unitsInResupply t ω = k} ∩ {ω | S.demandCount t ω = n}) =
      ∫⁻ ω in {ω | S.demandCount t ω = n}, np_F S t k (np_tv S t n ω) ∂P := by
  classical
  haveI := S.markLaw_isProb
  let Tv := np_tv S t n
  let Lv := fun ω => fun i : Fin n => S.mark i ω
  let Z := fun ω => (Tv ω, psumG S.gap n ω, psumG S.gap (n+1) ω)
  have hTm : Measurable Tv := np_tv_meas S ht n
  have hZm : Measurable Z := hTm.prodMk ((psumG_meas S.gap_measurable n).prodMk
    (psumG_meas S.gap_measurable (n+1)))
  have hLm : Measurable Lv := measurable_pi_lambda _ (fun i => S.mark_measurable i)
  let B := {ω | psumG S.gap n ω ≤ S.meanFn t ∧ S.meanFn t < psumG S.gap (n+1) ω}
  have hBm : MeasurableSet B :=
    (measurableSet_le (psumG_meas S.gap_measurable n) measurable_const).inter
      (measurableSet_lt measurable_const (psumG_meas S.gap_measurable (n+1)))
  rw [measure_congr (np_joint_ae S ht n k)]
  let Q := {p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → E) |
    (Finset.univ.filter (fun i => t < p.1.1 i + S.resupply (p.1.1 i) (p.2 i))).card = k ∧
      p.1.2.1 ≤ S.meanFn t ∧ S.meanFn t < p.1.2.2}
  have hcardR : Measurable (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → E) =>
      ((Finset.univ.filter (fun i => t < p.1.1 i + S.resupply (p.1.1 i) (p.2 i))).card : ℝ)) := by
    simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    refine Finset.measurable_sum _ (fun i _ => Measurable.ite ?_ measurable_const measurable_const)
    have hm1 : Measurable (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → E) => p.1.1 i) :=
      (measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)
    have hm2 : Measurable (fun p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → E) => p.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    exact measurableSet_lt measurable_const (hm1.add (S.resupply_measurable.comp (hm1.prodMk hm2)))
  have hQm : MeasurableSet Q := by
    have he : Q = {p : ((Fin n → ℝ) × ℝ × ℝ) × (Fin n → E) |
        ((Finset.univ.filter (fun i => t < p.1.1 i + S.resupply (p.1.1 i) (p.2 i))).card : ℝ) = (k : ℝ)} ∩
        ({p | p.1.2.1 ≤ S.meanFn t} ∩ {p | S.meanFn t < p.1.2.2}) := by
      ext p; simp only [Q, Set.mem_setOf_eq, Set.mem_inter_iff, Nat.cast_inj]
    rw [he]
    exact (measurableSet_eq_fun hcardR measurable_const).inter
      ((measurableSet_le (measurable_fst.comp (measurable_snd.comp measurable_fst)) measurable_const).inter
        (measurableSet_lt measurable_const (measurable_snd.comp (measurable_snd.comp measurable_fst))))
  have hpre : {ω | np_cnt S t n ω = k} ∩ B = (fun ω => (Z ω,Lv ω)) ⁻¹' Q := by
    ext ω; rfl
  have hslice : ∀ z : (Fin n → ℝ) × ℝ × ℝ, (P.map Lv) (Prod.mk z ⁻¹' Q) =
      Set.indicator {z : (Fin n → ℝ) × ℝ × ℝ | z.2.1 ≤ S.meanFn t ∧ S.meanFn t < z.2.2}
        (fun z => np_F S t k z.1) z := by
    intro z
    rw [np_marks_law S n]
    by_cases hz : z.2.1 ≤ S.meanFn t ∧ S.meanFn t < z.2.2
    · rw [Set.indicator_of_mem (by exact hz), ← np_pi_count S t k z.1]
      congr 1
      ext l; simp only [Set.mem_preimage, Q, Set.mem_setOf_eq, hz, and_true]
    · rw [Set.indicator_of_notMem (by exact hz)]
      have he : Prod.mk z ⁻¹' Q = ∅ := by
        ext l; simp only [Set.mem_preimage, Q, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro _ h1 h2; exact hz ⟨h1,h2⟩
      rw [he,measure_empty]
  have hBz : MeasurableSet {z : (Fin n → ℝ) × ℝ × ℝ | z.2.1 ≤ S.meanFn t ∧ S.meanFn t < z.2.2} :=
    (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))
  have hFm := np_F_meas S t k (n := n)
  have he : P ({ω | np_cnt S t n ω = k} ∩ B) = ∫⁻ ω in B, np_F S t k (Tv ω) ∂P := by
    rw [hpre, ← Measure.map_apply (hZm.prodMk hLm) hQm,
      (indepFun_iff_map_prod_eq_prod_map_map hZm.aemeasurable hLm.aemeasurable).1
        (np_joint_indep S ht n), Measure.prod_apply hQm]
    simp_rw [hslice]
    rw [lintegral_map (f := {z : (Fin n → ℝ) × ℝ × ℝ | z.2.1 ≤ S.meanFn t ∧ S.meanFn t < z.2.2}.indicator
        (fun z => np_F S t k z.1)) ((hFm.comp measurable_fst).indicator hBz) hZm,
      ← lintegral_indicator hBm]
    rfl
  rw [he, setLIntegral_congr (np_E_eq_N S ht n)]

lemma np_binomial_enn [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (hm : 0 < S.meanFn t) (n k : ℕ) :
    P ({ω | S.unitsInResupply t ω = k} ∩ {ω | S.demandCount t ω = n}) =
      (P {ω | S.demandCount t ω = n}) * (n.choose k : ℝ≥0∞) *
        ENNReal.ofReal (∫ s in (0:ℝ)..t, (1 - S.resupplyCdf s (t-s)) * (S.rate s / S.meanFn t)) ^ k *
        ENNReal.ofReal (1 - ∫ s in (0:ℝ)..t, (1 - S.resupplyCdf s (t-s)) * (S.rate s / S.meanFn t)) ^ (n-k) := by
  have ht : 0 < t := by
    by_contra h; push_neg at h; linarith [RS_meanFn_nonpos S h]
  haveI := np_arrival_prob S hm
  have hs : Measurable (fun x : Fin n → ℝ => x ∘ Tuple.sort x) := fun _ hA => sortset_meas hA
  rw [np_joint_integral S ht.le n k,
    ← lintegral_map (np_F_meas S t k) (np_tv_meas S ht.le n),
    np_tv_law S hm n, lintegral_smul_measure, lintegral_map (np_F_meas S t k) hs]
  simp only [np_F_perm]
  rw [np_F_integral, np_q_integral S hm, np_r_integral S hm]
  ring

end ServiceParts.NonstatPalm
open ServiceParts.NonstatPalm

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : ResupplySystem Ω P E)
    {t : ℝ} (hm : 0 < S.meanFn t) (n k : ℕ) :
    (P ({ω | S.unitsInResupply t ω = k} ∩ {ω | S.demandCount t ω = n})).toReal =
      (P {ω | S.demandCount t ω = n}).toReal *
        ((Nat.choose n k : ℝ) *
          (∫ s in (0 : ℝ)..t, (1 - S.resupplyCdf s (t - s)) * (S.rate s / S.meanFn t)) ^ k *
          (1 - ∫ s in (0 : ℝ)..t, (1 - S.resupplyCdf s (t - s)) * (S.rate s / S.meanFn t)) ^
            (n - k)) := by
  have ht : 0 < t := by
    by_contra h; push_neg at h; linarith [RS_meanFn_nonpos S h]
  let p := ∫ s in (0:ℝ)..t, (1-S.resupplyCdf s (t-s)) * (S.rate s / S.meanFn t)
  have he : p = S.alpha t / S.meanFn t := by
    simp only [p, div_eq_mul_inv, ← mul_assoc, intervalIntegral.integral_mul_const, ResupplySystem.alpha]
  have hp0 : 0 ≤ p := by rw [he]; exact div_nonneg (np_alpha_bounds S ht.le).1 hm.le
  have hp1 : p ≤ 1 := by rw [he]; exact (div_le_one hm).2 (np_alpha_bounds S ht.le).2
  rw [np_binomial_enn S hm n k]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  change (P {ω | S.demandCount t ω = n}).toReal * (n.choose k : ℝ) *
      (ENNReal.ofReal p).toReal ^ k * (ENNReal.ofReal (1-p)).toReal ^ (n-k) =
    (P {ω | S.demandCount t ω = n}).toReal * ((n.choose k : ℝ) * p ^ k * (1-p) ^ (n-k))
  rw [ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal (sub_nonneg.2 hp1)]
  ring
