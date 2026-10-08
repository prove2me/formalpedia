-- Prove2me | solution 1 for QueueingFundamentals.Foundations.poisson_count_cdf
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:56:43.624305+00:00
-- url     : https://prove2.me/submissions/08390624-e493-4c7b-8d82-60a1c74cebca

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess

open MeasureTheory ProbabilityTheory


namespace QueueingFundamentals.Foundations

open Set Filter Topology


lemma qfb_exp_noatoms (lam : ℝ) (x : ℝ) : expMeasure lam {x} = 0 := by
  unfold expMeasure gammaMeasure
  exact (withDensity_absolutelyContinuous _ _) (Real.volume_singleton)

lemma qfb_exp_Ioc (lam : ℝ) (hlam : 0 < lam) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    expMeasure lam (Ioc a b) = ENNReal.ofReal (Real.exp (-(lam * a)) - Real.exp (-(lam * b))) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [← measure_cdf (expMeasure lam), StieltjesFunction.measure_Ioc, cdf_expMeasure_eq hlam,
    cdf_expMeasure_eq hlam, if_pos ha, if_pos (ha.trans hab)]
  congr 1; ring

lemma qfb_exp_Ioi (lam : ℝ) (hlam : 0 < lam) (a : ℝ) (ha : 0 ≤ a) :
    expMeasure lam (Ioi a) = ENNReal.ofReal (Real.exp (-(lam * a))) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [← measure_cdf (expMeasure lam), StieltjesFunction.measure_Ioi _ (tendsto_cdf_atTop _),
    cdf_expMeasure_eq hlam, if_pos ha]
  congr 1; ring

/-- partial exponential sum -/
noncomputable def qfbR (lam : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (lam * s) ^ i / (i.factorial : ℝ)

lemma qfbR_zero_arg (lam : ℝ) (k : ℕ) : qfbR lam k 0 = 1 := by
  unfold qfbR
  rw [Finset.sum_range_succ']
  simp

lemma qfbR_succ (lam : ℝ) (k : ℕ) (s : ℝ) :
    qfbR lam (k + 1) s = 1 + ∑ i ∈ Finset.range (k + 1),
      (lam * s) ^ (i + 1) / ((i + 1).factorial : ℝ) := by
  unfold qfbR
  rw [Finset.sum_range_succ']
  simp [add_comm]

lemma qfbR_ge_one (lam : ℝ) (hlam : 0 < lam) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    1 ≤ qfbR lam k s := by
  cases k with
  | zero => simp [qfbR]
  | succ k =>
    rw [qfbR_succ]
    have : 0 ≤ ∑ i ∈ Finset.range (k + 1), (lam * s) ^ (i + 1) / ((i + 1).factorial : ℝ) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    linarith

lemma qfbR_nonneg (lam : ℝ) (hlam : 0 < lam) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ qfbR lam k s := le_trans zero_le_one (qfbR_ge_one lam hlam k s hs)

lemma qfbR_deriv (lam : ℝ) (k : ℕ) (s : ℝ) :
    HasDerivAt (qfbR lam (k + 1)) (lam * qfbR lam k s) s := by
  have h : ∀ i : ℕ, HasDerivAt (fun s => (lam * s) ^ (i + 1) / ((i + 1).factorial : ℝ))
      (lam * ((lam * s) ^ i / (i.factorial : ℝ))) s := by
    intro i
    have h1 : HasDerivAt (fun s => lam * s) lam s := by
      simpa using (hasDerivAt_id s).const_mul lam
    have h2 := (h1.pow (i + 1)).div_const ((i + 1).factorial : ℝ)
    refine h2.congr_deriv ?_
    rw [Nat.factorial_succ]
    have : (i.factorial : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hs0 : HasDerivAt (fun s => ∑ i ∈ Finset.range (k + 1),
      (lam * s) ^ (i + 1) / ((i + 1).factorial : ℝ))
      (∑ i ∈ Finset.range (k + 1), lam * ((lam * s) ^ i / (i.factorial : ℝ))) s :=
    HasDerivAt.fun_sum (fun i _ => h i)
  have hs := hs0.const_add 1
  have heq : qfbR lam (k + 1) = fun s => 1 + ∑ i ∈ Finset.range (k + 1),
      (lam * s) ^ (i + 1) / ((i + 1).factorial : ℝ) := by
    funext s; exact qfbR_succ lam k s
  rw [heq]
  refine hs.congr_deriv ?_
  unfold qfbR
  rw [Finset.mul_sum]

lemma qfbR_cont (lam : ℝ) (k : ℕ) : Continuous (qfbR lam k) := by
  unfold qfbR; fun_prop

lemma qfb_int (lam : ℝ) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ y in (0 : ℝ)..t, lam * qfbR lam k (t - y) * Real.exp (-(lam * t)) =
      (qfbR lam (k + 1) t - 1) * Real.exp (-(lam * t)) := by
  have hd : ∀ y ∈ Set.uIcc (0 : ℝ) t, HasDerivAt
      (fun y => -qfbR lam (k + 1) (t - y) * Real.exp (-(lam * t)))
      (lam * qfbR lam k (t - y) * Real.exp (-(lam * t))) y := by
    intro y _
    have h1 := (qfbR_deriv lam k (t - y)).comp_const_sub t y
    have h2 := (h1.neg).mul_const (Real.exp (-(lam * t)))
    refine h2.congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp only [sub_self, sub_zero, qfbR_zero_arg]; ring
  · apply Continuous.intervalIntegrable
    have := qfbR_cont lam k
    fun_prop

lemma qfb_step {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (lam : ℝ) (hlam : 0 < lam) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y μ) (hYlaw : μ.map Y = expMeasure lam) (k : ℕ)
    (hpos : ∀ s : ℝ, 0 ≤ s → μ {ω | s < X ω} =
      ENNReal.ofReal (qfbR lam k s * Real.exp (-(lam * s))))
    (hneg : ∀ s : ℝ, s < 0 → μ {ω | s < X ω} = 1) (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | t < X ω + Y ω} =
      ENNReal.ofReal (qfbR lam (k + 1) t * Real.exp (-(lam * t))) := by
  have hmeasS : MeasurableSet {p : ℝ × ℝ | t < p.1 + p.2} :=
    measurableSet_lt measurable_const (measurable_fst.add measurable_snd)
  have e1 : μ {ω | t < X ω + Y ω} =
      (μ.map (fun ω => (X ω, Y ω))) {p : ℝ × ℝ | t < p.1 + p.2} := by
    rw [Measure.map_apply (hX.prodMk hY) hmeasS]; rfl
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [e1, (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hind, hYlaw,
    Measure.prod_apply_symm hmeasS]
  have hφ : ∀ y : ℝ, (μ.map X) ((fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | t < p.1 + p.2}) =
      μ {ω | t - y < X ω} := by
    intro y
    rw [Measure.map_apply hX (measurable_prodMk_right hmeasS)]
    congr 1; ext ω; simp only [mem_preimage, mem_setOf_eq]
    constructor <;> intro h <;> linarith
  simp_rw [hφ]
  have hφm : Measurable (fun y => μ {ω | t - y < X ω}) := by
    apply Monotone.measurable
    intro y1 y2 hy
    apply measure_mono
    intro ω (h : t - y1 < X ω)
    show t - y2 < X ω
    linarith
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [← lintegral_add_compl _ (measurableSet_Ioi (a := t))]
  have hA : ∫⁻ y in Ioi t, μ {ω | t - y < X ω} ∂(expMeasure lam) =
      ENNReal.ofReal (Real.exp (-(lam * t))) := by
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => (1 : ENNReal))
      (fun y hy => hneg (t - y) (by simp only [mem_Ioi] at hy; linarith))]
    rw [lintegral_one, Measure.restrict_apply_univ]
    have h := qfb_exp_Ioi lam hlam t ht
    exact h
  have hpdfm : Measurable (exponentialPDF lam) := (measurable_exponentialPDFReal lam).ennreal_ofReal
  have hE : expMeasure lam = volume.withDensity (exponentialPDF lam) := rfl
  have hB : ∫⁻ y in (Ioi t)ᶜ, μ {ω | t - y < X ω} ∂(expMeasure lam) =
      ENNReal.ofReal ((qfbR lam (k + 1) t - 1) * Real.exp (-(lam * t))) := by
    rw [compl_Ioi, hE, setLIntegral_withDensity_eq_setLIntegral_mul _ hpdfm hφm measurableSet_Iic]
    have hsplit : Iic t = Iio 0 ∪ Icc 0 t := by
      ext y; simp only [mem_Iic, mem_union, mem_Iio, mem_Icc]
      constructor
      · intro h; by_cases h0 : y < 0
        · exact Or.inl h0
        · exact Or.inr ⟨not_lt.mp h0, h⟩
      · rintro (h | h)
        · linarith
        · exact h.2
    have hdisj : Disjoint (Iio (0 : ℝ)) (Icc 0 t) :=
      Set.disjoint_left.mpr (fun y h1 h2 => by simp only [mem_Iio] at h1; linarith [h2.1])
    rw [hsplit, lintegral_union measurableSet_Icc hdisj]
    rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => (0 : ENNReal))
      (fun y hy => by simp [exponentialPDF_of_neg (show y < 0 from hy)])]
    rw [lintegral_zero, zero_add]
    rw [setLIntegral_congr_fun measurableSet_Icc
      (g := fun y => ENNReal.ofReal (lam * qfbR lam k (t - y) * Real.exp (-(lam * t))))
      (fun y hy => by
        simp only [Pi.mul_apply]
        rw [exponentialPDF_of_nonneg hy.1, hpos (t - y) (by linarith [hy.2]),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : Real.exp (-(lam * y)) * Real.exp (-(lam * (t - y))) = Real.exp (-(lam * t)) := by
          rw [← Real.exp_add]; congr 1; ring
        calc lam * Real.exp (-(lam * y)) * (qfbR lam k (t - y) * Real.exp (-(lam * (t - y))))
            = lam * qfbR lam k (t - y) * (Real.exp (-(lam * y)) *
              Real.exp (-(lam * (t - y)))) := by ring
          _ = _ := by rw [this])]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht, qfb_int lam k t ht]
    · apply Continuous.integrableOn_Icc
      have := qfbR_cont lam k
      fun_prop
    · apply ae_restrict_of_forall_mem measurableSet_Icc
      intro y hy
      have := qfbR_nonneg lam hlam k (t - y) (by linarith [hy.2])
      show 0 ≤ lam * qfbR lam k (t - y) * Real.exp (-(lam * t))
      positivity
  rw [hA, hB, ← ENNReal.ofReal_add (by positivity)]
  · congr 1; ring
  · have := qfbR_ge_one lam hlam (k + 1) t ht
    have := Real.exp_pos (-(lam * t))
    nlinarith

lemma qfbQ_deriv (lam : ℝ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x => -(qfbR lam n x * Real.exp (-(lam * x))))
      (lam * (lam * x) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * x))) x := by
  have he : HasDerivAt (fun x => Real.exp (-(lam * x))) (Real.exp (-(lam * x)) * (-lam)) x := by
    have h1 : HasDerivAt (fun x => -(lam * x)) (-lam) x :=
      (((hasDerivAt_id x).const_mul lam).neg).congr_deriv (by simp)
    exact h1.exp
  cases n with
  | zero =>
    have h0 : qfbR lam 0 = fun _ => 1 := by funext x; simp [qfbR]
    rw [h0]
    have := he.neg
    simp only [one_mul]
    refine this.congr_deriv ?_
    simp; ring
  | succ k =>
    have h := ((qfbR_deriv lam k x).mul he).neg
    refine h.congr_deriv ?_
    have : qfbR lam (k + 1) x = qfbR lam k x + (lam * x) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
      unfold qfbR; rw [Finset.sum_range_succ (n := k + 1)]
    rw [this]; ring

lemma qfbQ_tendsto (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Tendsto (fun x => -(qfbR lam n x * Real.exp (-(lam * x)))) atTop (𝓝 0) := by
  have : (fun x => qfbR lam n x * Real.exp (-(lam * x))) = fun x =>
      ∑ i ∈ Finset.range (n + 1), (1 / (i.factorial : ℝ)) * ((lam * x) ^ i * Real.exp (-(lam * x))) := by
    funext x; unfold qfbR; rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro i _; ring
  suffices h : Tendsto (fun x => qfbR lam n x * Real.exp (-(lam * x))) atTop (𝓝 0) by
    simpa using h.neg
  rw [this]
  rw [show (0 : ℝ) = ∑ i ∈ Finset.range (n + 1), (1 / (i.factorial : ℝ)) * 0 by simp]
  apply tendsto_finset_sum
  intro i _
  apply Tendsto.const_mul
  exact (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i).comp
    (tendsto_id.const_mul_atTop hlam)

lemma qfb_integral_Ioi (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∫ x in Ioi t, lam * (lam * x) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * x)) =
      qfbR lam n t * Real.exp (-(lam * t)) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => qfbQ_deriv lam n x)
    (integrableOn_Ioi_deriv_of_nonneg' (fun x _ => qfbQ_deriv lam n x)
      (fun x hx => by
        have : 0 ≤ lam * x := mul_nonneg hlam.le (ht.trans (mem_Ioi.mp hx).le)
        exact mul_nonneg (div_nonneg (mul_nonneg hlam.le (pow_nonneg this n)) (by positivity))
          (Real.exp_pos _).le) (qfbQ_tendsto lam hlam n)) (qfbQ_tendsto lam hlam n)]
  ring

lemma qfbR_tendsto (lam t : ℝ) :
    Tendsto (fun m : ℕ => qfbR lam m t * Real.exp (-(lam * t))) atTop (𝓝 1) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (lam * t)).tendsto_sum_nat
  rw [← congrFun Real.exp_eq_exp_ℝ] at h
  have h2 := (h.comp (tendsto_add_atTop_nat 1)).mul_const (Real.exp (-(lam * t)))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
  exact h2

section Arr
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ) (hT : IsExpInterarrivals μ lam T)

include hlam hT in
lemma qfb_T_nonpos_null (i : ℕ) : μ {ω | T i ω ≤ 0} = 0 := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [show {ω | T i ω ≤ 0} = T i ⁻¹' Iic 0 from rfl,
    ← Measure.map_apply (hT.measurable i) measurableSet_Iic, hT.law i, ← ofReal_cdf,
    cdf_expMeasure_eq hlam, if_pos le_rfl]
  simp

include hlam hT in
lemma qfb_bad_null : μ (⋃ i, {ω | T i ω ≤ 0}) = 0 :=
  measure_iUnion_null (fun i => qfb_T_nonpos_null μ lam hlam T hT i)

lemma qfb_arr_meas (hT : IsExpInterarrivals μ lam T) (k : ℕ) : Measurable (arrivalTime T k) := by
  have : arrivalTime T k = fun ω => ∑ i ∈ Finset.range k, T i ω := rfl
  rw [this]
  exact Finset.measurable_sum _ (fun i _ => hT.measurable i)

include hlam hT in
lemma qfb_surv_neg (k : ℕ) (s : ℝ) (hs : s < 0) :
    μ {ω | s < arrivalTime T (k + 1) ω} = 1 := by
  have hm : MeasurableSet {ω | s < arrivalTime T (k + 1) ω} :=
    measurableSet_lt measurable_const (qfb_arr_meas μ lam T hT (k + 1))
  rw [← prob_compl_eq_zero_iff hm]
  apply measure_mono_null _ (qfb_bad_null μ lam hlam T hT)
  intro ω hω
  simp only [mem_compl_iff, mem_setOf_eq, not_lt] at hω
  simp only [mem_iUnion, mem_setOf_eq]
  by_contra hcon
  push_neg at hcon
  have : 0 < arrivalTime T (k + 1) ω :=
    Finset.sum_pos (fun i _ => hcon i) ⟨0, by simp⟩
  linarith

include hlam hT in
lemma qfb_surv (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    μ {ω | s < arrivalTime T (k + 1) ω} =
      ENNReal.ofReal (qfbR lam k s * Real.exp (-(lam * s))) := by
  induction k generalizing s with
  | zero =>
    haveI := isProbabilityMeasure_expMeasure hlam
    have h1 : {ω | s < arrivalTime T (0 + 1) ω} = T 0 ⁻¹' Ioi s := by
      ext ω; simp [arrivalTime]
    rw [h1, ← Measure.map_apply (hT.measurable 0) measurableSet_Ioi, hT.law 0,
      qfb_exp_Ioi lam hlam s hs]
    simp [qfbR]
  | succ k ih =>
    have hind : IndepFun (arrivalTime T (k + 1)) (T (k + 1)) μ := by
      have h := hT.indep.indepFun_finsetSum_of_notMem hT.measurable
        (s := Finset.range (k + 1)) (i := k + 1) (by simp)
      have he : (∑ j ∈ Finset.range (k + 1), T j) = arrivalTime T (k + 1) := by
        funext ω; simp [arrivalTime, Finset.sum_apply]
      rwa [he] at h
    have h1 : {ω | s < arrivalTime T (k + 1 + 1) ω} =
        {ω | s < arrivalTime T (k + 1) ω + T (k + 1) ω} := by
      ext ω; simp [arrivalTime, Finset.sum_range_succ (n := k + 1)]
    rw [h1]
    exact qfb_step μ lam hlam _ _ (qfb_arr_meas μ lam T hT (k + 1)) (hT.measurable (k + 1))
      hind (hT.law (k + 1)) k ih (qfb_surv_neg μ lam hlam T hT k) s hs

include hlam hT in
lemma qfb_inf_null (t : ℝ) (ht : 0 ≤ t) : μ {ω | ∀ m, arrivalTime T m ω ≤ t} = 0 := by
  have hb : ∀ m : ℕ, μ {ω | ∀ m, arrivalTime T m ω ≤ t} ≤
      ENNReal.ofReal (1 - qfbR lam m t * Real.exp (-(lam * t))) := by
    intro m
    have hm : MeasurableSet {ω | t < arrivalTime T (m + 1) ω} :=
      measurableSet_lt measurable_const (qfb_arr_meas μ lam T hT (m + 1))
    calc μ {ω | ∀ m, arrivalTime T m ω ≤ t} ≤ μ {ω | t < arrivalTime T (m + 1) ω}ᶜ := by
          apply measure_mono
          intro ω hω
          simp only [mem_compl_iff, mem_setOf_eq, not_lt]
          exact hω (m + 1)
      _ = _ := by
          rw [prob_compl_eq_one_sub hm, qfb_surv μ lam hlam T hT m t ht,
            ENNReal.ofReal_sub _ (by
              have := qfbR_nonneg lam hlam m t ht; positivity), ENNReal.ofReal_one]
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (1 - qfbR lam m t * Real.exp (-(lam * t))))
      atTop (𝓝 (ENNReal.ofReal 0)) := by
    apply ENNReal.tendsto_ofReal
    have := (qfbR_tendsto lam t).const_sub 1
    simpa using this
  rw [ENNReal.ofReal_zero] at hlim
  exact le_antisymm (ge_of_tendsto' hlim hb) bot_le

lemma qfb_arr_mono (ω : Ω) (hpos : ∀ i, 0 < T i ω) (a b : ℕ) (hab : a ≤ b) :
    arrivalTime T a ω ≤ arrivalTime T b ω :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hab)
    (fun i _ _ => (hpos i).le)

lemma qfb_count_iff (t : ℝ) (ω : Ω) (hpos : ∀ i, 0 < T i ω)
    (hfin : ∃ m, t < arrivalTime T m ω) (n : ℕ) :
    countingProcess T t ω ≤ n ↔ t < arrivalTime T (n + 1) ω := by
  unfold countingProcess
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨m, hm⟩ := hfin
    have hsub1 : {k : ℕ | 1 ≤ k ∧ arrivalTime T k ω ≤ t} ⊆ (Finset.range m : Set ℕ) := by
      intro k ⟨_, hk⟩
      simp only [Finset.coe_range, mem_Iio]
      by_contra hkm
      push_neg at hkm
      have := qfb_arr_mono T ω hpos m k hkm
      linarith
    have hsub2 : ((Finset.Icc 1 (n + 1) : Finset ℕ) : Set ℕ) ⊆
        {k : ℕ | 1 ≤ k ∧ arrivalTime T k ω ≤ t} := by
      intro k hk
      simp only [Finset.coe_Icc, mem_Icc] at hk
      exact ⟨hk.1, le_trans (qfb_arr_mono T ω hpos k (n + 1) hk.2) hcon⟩
    have := Set.ncard_le_ncard hsub2 ((Finset.range m).finite_toSet.subset hsub1)
    rw [Set.ncard_coe_finset, Nat.card_Icc] at this
    omega
  · intro h
    have hsub : {k : ℕ | 1 ≤ k ∧ arrivalTime T k ω ≤ t} ⊆ ((Finset.Icc 1 n : Finset ℕ) : Set ℕ) := by
      intro k ⟨hk1, hk⟩
      simp only [Finset.coe_Icc, mem_Icc]
      refine ⟨hk1, ?_⟩
      by_contra hkn
      push_neg at hkn
      have := qfb_arr_mono T ω hpos (n + 1) k hkn
      linarith
    have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Nat.card_Icc] at this
    omega

include hlam hT in
lemma qfb_good_ae (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂μ, (∀ i, 0 < T i ω) ∧ ∃ m, t < arrivalTime T m ω := by
  rw [ae_iff]
  apply measure_mono_null _ (measure_union_null (qfb_bad_null μ lam hlam T hT)
    (qfb_inf_null μ lam hlam T hT t ht))
  intro ω hω
  simp only [mem_setOf_eq, not_and_or, not_forall, not_exists, not_lt] at hω
  rcases hω with ⟨i, hi⟩ | h
  · exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
  · exact Or.inr h

include hlam hT in
lemma qfb_le_aeq (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    {ω | countingProcess T t ω ≤ n} =ᵐ[μ] {ω | t < arrivalTime T (n + 1) ω} := by
  apply Filter.Eventually.set_eq
  filter_upwards [qfb_good_ae μ lam hlam T hT t ht] with ω hω
  exact qfb_count_iff T t ω hω.1 hω.2 n

include hlam hT in
lemma qfb_le_ae (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    μ {ω | countingProcess T t ω ≤ n} = μ {ω | t < arrivalTime T (n + 1) ω} :=
  measure_congr (qfb_le_aeq μ lam hlam T hT t ht n)

end Arr

lemma qfb_sum_form (lam t : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (lam * t) ^ i * Real.exp (-(lam * t)) / (i.factorial : ℝ) =
      qfbR lam n t * Real.exp (-(lam * t)) := by
  unfold qfbR; rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _; ring

theorem poisson_count_cdf_core {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | countingProcess T t ω ≤ n}).toReal =
        ∫ x in Set.Ioi t, lam * (lam * x) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * x)) ∧
      (μ {ω | countingProcess T t ω ≤ n}).toReal =
        ∑ i ∈ Finset.range (n + 1), (lam * t) ^ i * Real.exp (-(lam * t)) / (i.factorial : ℝ) ∧
      (μ {ω | countingProcess T t ω = n}).toReal =
        (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * t)) := by
  have hle : ∀ m : ℕ, (μ {ω | countingProcess T t ω ≤ m}).toReal =
      qfbR lam m t * Real.exp (-(lam * t)) := by
    intro m
    rw [qfb_le_ae μ lam hlam T hT t ht m, qfb_surv μ lam hlam T hT m t ht,
      ENNReal.toReal_ofReal (by have := qfbR_nonneg lam hlam m t ht; positivity)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hle n, qfb_integral_Ioi lam hlam n t ht]
  · rw [hle n, qfb_sum_form]
  · cases n with
    | zero =>
      have : {ω | countingProcess T t ω = 0} = {ω | countingProcess T t ω ≤ 0} := by
        ext ω; simp
      rw [this, hle 0]; simp [qfbR]
    | succ m =>
      have hsub : {ω | countingProcess T t ω ≤ m} ⊆ {ω | countingProcess T t ω ≤ m + 1} :=
        fun ω (h : countingProcess T t ω ≤ m) => (show countingProcess T t ω ≤ m + 1 by omega)
      have hdiff : {ω | countingProcess T t ω ≤ m + 1} =
          {ω | countingProcess T t ω = m + 1} ∪ {ω | countingProcess T t ω ≤ m} := by
        ext ω; simp only [mem_setOf_eq, mem_union]; omega
      have hu : μ {ω | countingProcess T t ω ≤ m + 1} =
          μ {ω | countingProcess T t ω = m + 1} + μ {ω | countingProcess T t ω ≤ m} := by
        rw [hdiff]
        have hm : MeasurableSet {ω | t < arrivalTime T (m + 1) ω} :=
          measurableSet_lt measurable_const (qfb_arr_meas μ lam T hT (m + 1))
        have hnm : NullMeasurableSet {ω | countingProcess T t ω ≤ m} μ :=
          hm.nullMeasurableSet.congr (qfb_le_aeq μ lam hlam T hT t ht m).symm
        apply measure_union₀ hnm
        apply Disjoint.aedisjoint
        exact Set.disjoint_left.mpr (fun ω (h1 : countingProcess T t ω = m + 1)
          (h2 : countingProcess T t ω ≤ m) => by omega)
      have h2 := congrArg ENNReal.toReal hu
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hle, hle] at h2
      have : qfbR lam (m + 1) t = qfbR lam m t + (lam * t) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
        unfold qfbR; rw [Finset.sum_range_succ (n := m + 1)]
      rw [this] at h2
      linarith

end QueueingFundamentals.Foundations

open QueueingFundamentals.Foundations


theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (lam : ℝ) (hlam : 0 < lam) (T : ℕ → Ω → ℝ)
    (hT : IsExpInterarrivals μ lam T) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | countingProcess T t ω ≤ n}).toReal =
        ∫ x in Set.Ioi t, lam * (lam * x) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * x)) ∧
      (μ {ω | countingProcess T t ω ≤ n}).toReal =
        ∑ i ∈ Finset.range (n + 1), (lam * t) ^ i * Real.exp (-(lam * t)) / (i.factorial : ℝ) ∧
      (μ {ω | countingProcess T t ω = n}).toReal =
        (lam * t) ^ n / (n.factorial : ℝ) * Real.exp (-(lam * t)) := by
  exact poisson_count_cdf_core μ lam hlam T hT n t ht
