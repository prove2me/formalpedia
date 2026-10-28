-- Prove2me | solution 1 for ServiceParts.NonstatPalm.nonstationary_palm
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:54:17.615014+00:00
-- url     : https://prove2.me/submissions/644e0746-30e3-4847-bc0f-0a111c080e80

-- Count helpers reused from accepted submission 32be2b68-1bb8-4771-9ae8-4af42acb4ec1.
-- Inverse-time helpers reused from accepted submission 297117c6-888f-4ec2-bf9c-e4eeb746d3d5.
import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_ResupplySystem
import Theorems.Thm_ServiceParts_NonstatPalm_units_binomial_given_count

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

lemma np_units_zero [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (ht : 0 ≤ t) (hm : S.meanFn t = 0) : ∀ᵐ ω ∂P, S.unitsInResupply t ω = 0 := by
  have hcount : P {ω | S.demandCount t ω = 0} = 1 := by
    change P {ω | cntG S.gap (S.meanFn t) ω = 0} = 1
    rw [cntG_poisson S.gap_measurable (RS_gap_law S) (RS_gap_indep S) (meanFn_nonneg S ht), hm]
    simp
  have hnm : NullMeasurableSet {ω | S.demandCount t ω = 0} P := by
    refine NullMeasurableSet.congr
      (s := {ω | S.meanFn t < psumG S.gap 1 ω} \ {ω | S.meanFn t < psumG S.gap 0 ω})
      ?_ (Filter.eventuallyEq_set.2 ?_)
    · exact ((measurableSet_lt measurable_const (psumG_meas S.gap_measurable 1)).diff
        (measurableSet_lt measurable_const (psumG_meas S.gap_measurable 0))).nullMeasurableSet
    · filter_upwards [cntG_ae S.gap_measurable (RS_gap_law S) (RS_gap_indep S)
        (meanFn_nonneg S ht)] with ω hω
      exact (hω 0).symm
  have hN : ∀ᵐ ω ∂P, S.demandCount t ω = 0 := by
    exact (mem_ae_iff_prob_eq_one₀ hnm).2 hcount
  filter_upwards [hN, gapG_nonneg_ae S.gap_measurable (RS_gap_law S),
    finiteG_ae S.gap_measurable (RS_gap_law S) (RS_gap_indep S) (meanFn_nonneg S ht)] with ω hN hω hK
  have h := (cntG_iff (meanFn_nonneg S ht) hω hK 0).1 hN
  rw [np_units_eq S hω h]
  simp [np_cnt]

lemma np_positive_core [IsProbabilityMeasure P] (S : ResupplySystem Ω P E) {t : ℝ}
    (ht : 0 ≤ t) (hm : 0 < S.meanFn t) (x : ℕ) :
    (P {ω | S.unitsInResupply t ω = x}).toReal =
      Real.exp (-S.alpha t) * S.alpha t ^ x / (Nat.factorial x : ℝ) := by
  set f : ℕ → Set Ω := fun n => {ω | S.unitsInResupply t ω = x} ∩ {ω | S.demandCount t ω = n}
  have hU : {ω | S.unitsInResupply t ω = x} = ⋃ n, f n := by
    ext ω
    simp only [f, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨_, h, _⟩; exact h
  have hdisj : Pairwise (Function.onFun (AEDisjoint P) f) := by
    intro a b hab
    refine Disjoint.aedisjoint ?_
    rw [Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    exact hab (h1.symm.trans h2)
  rw [hU, measure_iUnion₀ hdisj (fun n => np_joint_nullmeas S ht n x),
    ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _)]
  simp only [f, units_binomial_given_count S hm, np_count_real S ht]
  set a := S.meanFn t with ha
  set p := ∫ s in (0:ℝ)..t, (1-S.resupplyCdf s (t-s)) * (S.rate s / S.meanFn t) with hp
  have hap : S.alpha t = a * p := by
    have he : p = S.alpha t / a := by
      simp only [hp, div_eq_mul_inv, ← mul_assoc, intervalIntegral.integral_mul_const,
        ResupplySystem.alpha, ha]
    rw [he]
    field_simp
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
end ServiceParts.NonstatPalm

open ServiceParts.NonstatPalm

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : ResupplySystem Ω P E)
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (P {ω | S.unitsInResupply t ω = k}).toReal =
      Real.exp (-S.alpha t) * S.alpha t ^ k / (Nat.factorial k : ℝ) := by
  rcases (meanFn_nonneg S ht).eq_or_lt with hm | hm
  · have hm0 : S.meanFn t = 0 := hm.symm
    have ha : S.alpha t = 0 := by
      have := np_alpha_bounds S ht
      rw [hm0] at this
      exact le_antisymm this.2 this.1
    have he : ({ω | S.unitsInResupply t ω = k} : Set Ω) =ᵐ[P] {ω | 0 = k} := by
      refine Filter.eventuallyEq_set.2 ?_
      filter_upwards [np_units_zero S ht hm0] with ω hω
      simp only [Set.mem_setOf_eq, hω]
    rw [measure_congr he, ha]
    rcases k with _ | k <;> simp
  · exact np_positive_core S ht hm k
