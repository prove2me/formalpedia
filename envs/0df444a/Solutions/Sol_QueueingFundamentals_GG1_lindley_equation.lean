-- Prove2me | solution 1 for QueueingFundamentals.GG1.lindley_equation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:10:05.691013+00:00
-- url     : https://prove2.me/submissions/2263291e-9562-4fbb-b7a4-4059d4a8c560

import Mathlib
import Definitions.Def_QueueingFundamentals_GG1_Lindley



namespace QueueingFundamentals.GG1

open MeasureTheory

lemma qf_diffLaw_prob (A B : Measure ℝ) [IsProbabilityMeasure A] [IsProbabilityMeasure B] :
    IsProbabilityMeasure (diffLaw A B) := by
  unfold diffLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma qf_cdf_mono (ν : Measure ℝ) [IsFiniteMeasure ν] : Monotone (cdfOf ν) := by
  intro a b hab
  unfold cdfOf
  exact measureReal_mono (Set.Iic_subset_Iic.mpr hab)

lemma qf_cdf_meas (ν : Measure ℝ) [IsFiniteMeasure ν] : Measurable (cdfOf ν) :=
  (qf_cdf_mono ν).measurable

lemma qf_cdf_nonneg (ν : Measure ℝ) (t : ℝ) : 0 ≤ cdfOf ν t := by
  unfold cdfOf; exact measureReal_nonneg

lemma qf_cdf_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) : cdfOf ν t ≤ 1 := by
  unfold cdfOf; exact measureReal_le_one

lemma qf_stat_neg {U ν : Measure ℝ} (h : lindleyStep U ν = ν) (t : ℝ) (ht : t < 0) :
    cdfOf ν t = 0 := by
  unfold cdfOf
  rw [← h]
  unfold lindleyStep
  rw [measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Iic]
  have : (fun p : ℝ × ℝ => max 0 (p.1 + p.2)) ⁻¹' Set.Iic t = ∅ := by
    ext p; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
    exact lt_of_lt_of_le ht (le_max_left _ _)
  rw [this]; simp

lemma qf_stat_pos {U ν : Measure ℝ} [IsProbabilityMeasure U] [IsProbabilityMeasure ν]
    (h : lindleyStep U ν = ν) (t : ℝ) (ht : 0 ≤ t) :
    cdfOf ν t = ∫ x, cdfOf ν (t - x) ∂U := by
  have key : ν (Set.Iic t) = ∫⁻ x, ν (Set.Iic (t - x)) ∂U := by
    conv_lhs => rw [← h]
    unfold lindleyStep
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    rw [Measure.prod_apply_symm]
    · congr 1; ext x; congr 1; ext w
      simp only [Set.mem_preimage, Set.mem_Iic, max_le_iff, ht, true_and]
      constructor <;> intro hh <;> linarith
    · exact (measurableSet_Iic).preimage (by fun_prop)
  unfold cdfOf
  rw [measureReal_def, key]
  simp only [measureReal_def]
  refine (integral_toReal ?_ ?_).symm
  · have : Antitone (fun x => ν (Set.Iic (t - x))) := by
      intro a b hab; exact measure_mono (Set.Iic_subset_Iic.mpr (by linarith))
    exact this.measurable.aemeasurable
  · exact Filter.Eventually.of_forall (fun x => measure_lt_top _ _)

lemma qf_full_eq_Iic (ν : Measure ℝ) (U : Measure ℝ) (hneg : ∀ t, t < 0 → cdfOf ν t = 0) (t : ℝ) :
    ∫ x in Set.Iic t, cdfOf ν (t - x) ∂U = ∫ x, cdfOf ν (t - x) ∂U := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp only [Set.mem_Iic, not_le] at hx
  exact hneg _ (by linarith)

lemma qf_part1 {U ν : Measure ℝ} [IsProbabilityMeasure U] [IsProbabilityMeasure ν]
    (h : lindleyStep U ν = ν) (t : ℝ) :
    negPart U (cdfOf ν) t + cdfOf ν t = ∫ x in Set.Iic t, cdfOf ν (t - x) ∂U := by
  unfold negPart
  split_ifs with ht
  · rw [qf_stat_neg h t ht]; ring
  · rw [zero_add, qf_full_eq_Iic ν U (qf_stat_neg h) t]
    exact qf_stat_pos h t (not_lt.mp ht)

lemma qf_lap_int (ν : Measure ℝ) [IsProbabilityMeasure ν] (hneg : ∀ t, t < 0 → cdfOf ν t = 0)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * (cdfOf ν t : ℂ)) volume := by
  have hg : Integrable (Set.indicator (Set.Ici (0:ℝ)) (fun t => Real.exp (-s.re * t))) volume := by
    have h1 := exp_neg_integrableOn_Ioi 0 hs
    rw [← integrableOn_Ici_iff_integrableOn_Ioi] at h1
    exact h1.integrable_indicator measurableSet_Ici
  refine Integrable.mono' hg ?_ ?_
  · have := qf_cdf_meas ν
    exact (Measurable.mul (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun t => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hre : (-s * (t : ℂ)).re = -s.re * t := by simp
    rw [hre]
    by_cases ht : t < 0
    · rw [hneg t ht, abs_zero, mul_zero]
      exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    · rw [Set.indicator_of_mem (by simpa using not_lt.mp ht)]
      rw [abs_of_nonneg (qf_cdf_nonneg ν t)]
      have := qf_cdf_le_one ν t
      have := Real.exp_pos (-s.re * t)
      nlinarith

lemma qf_lifetime_exp_int (B : Measure ℝ) [IsProbabilityMeasure B] (hB : B (Set.Iio 0) = 0)
    (σ : ℝ) (hσ : 0 < σ) : Integrable (fun x => Real.exp (-σ * x)) B := by
  refine Integrable.mono' (integrable_const (1:ℝ)) (by fun_prop) ?_
  have := measure_eq_zero_iff_ae_notMem.mp hB
  filter_upwards [this] with x hx
  simp only [Set.mem_Iio, not_lt] at hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  nlinarith

lemma qf_expU_int (A B : Measure ℝ) [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (hB : B (Set.Iio 0) = 0) (σ : ℝ) (hσ : 0 < σ)
    (hA : Integrable (fun x : ℝ => Real.exp (σ * x)) A) :
    Integrable (fun x => Real.exp (-σ * x)) (diffLaw A B) := by
  unfold diffLaw
  rw [integrable_map_measure (by fun_prop) (by fun_prop)]
  have := (qf_lifetime_exp_int B hB σ hσ).mul_prod hA
  refine this.congr (Filter.Eventually.of_forall (fun p => ?_))
  simp only [Function.comp]
  rw [← Real.exp_add]; congr 1; ring

lemma qf_lst_diff (A B : Measure ℝ) [IsFiniteMeasure A] [IsFiniteMeasure B] (s : ℂ) :
    QueueingFundamentals.MG1.lst (diffLaw A B) s =
      QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s := by
  unfold QueueingFundamentals.MG1.lst diffLaw
  rw [integral_map (by fun_prop) (by fun_prop)]
  have : ∀ p : ℝ × ℝ, Complex.exp (-(s * ((p.1 - p.2 : ℝ) : ℂ))) =
      Complex.exp (-(s * (p.1 : ℂ))) * Complex.exp (-(-s * (p.2 : ℂ))) := by
    intro p; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [this]
  exact (integral_prod_mul (fun x : ℝ => Complex.exp (-(s * (x:ℂ)))) (fun y : ℝ => Complex.exp (-(-s*(y:ℂ))))).trans (mul_comm _ _)

lemma qf_lap_conv (U ν : Measure ℝ) [IsProbabilityMeasure U] [IsProbabilityMeasure ν]
    (hneg : ∀ t, t < 0 → cdfOf ν t = 0) (s : ℂ) (hs : 0 < s.re)
    (hU : Integrable (fun x => Real.exp (-s.re * x)) U) :
    Integrable (fun t : ℝ => Complex.exp (-s * (t : ℂ)) * ((∫ x, cdfOf ν (t - x) ∂U : ℝ) : ℂ)) volume ∧
    twoSidedLaplace (fun t => ∫ x, cdfOf ν (t - x) ∂U) s =
      twoSidedLaplace (cdfOf ν) s * QueueingFundamentals.MG1.lst U s := by
  set h : ℝ → ℂ := fun t => Complex.exp (-s * (t : ℂ)) * (cdfOf ν t : ℂ) with hh
  have hint : Integrable h volume := qf_lap_int ν hneg s hs
  set F : ℝ × ℝ → ℂ := fun p => Complex.exp (-s * (p.2 : ℂ)) * (cdfOf ν (p.2 - p.1) : ℂ) with hF
  have hFeq : ∀ x t : ℝ, F (x, t) = Complex.exp (-s * (x : ℂ)) * h (t - x) := by
    intro x t
    simp only [hF, hh]
    rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
  have hmeas : AEStronglyMeasurable F (U.prod volume) := by
    have := qf_cdf_meas ν
    exact (Measurable.mul (by fun_prop) (by fun_prop)).aestronglyMeasurable
  have hFint : Integrable F (U.prod volume) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · refine Filter.Eventually.of_forall (fun x => ?_)
      simp_rw [hFeq]
      exact (hint.comp_sub_right x).const_mul _
    · have : (fun x => ∫ t, ‖F (x, t)‖) = fun x => Real.exp (-s.re * x) * ∫ u, ‖h u‖ := by
        funext x
        simp_rw [hFeq, norm_mul, Complex.norm_exp]
        rw [integral_const_mul, integral_sub_right_eq_self (fun u => ‖h u‖) x]
        congr 2; simp
      rw [this]
      exact hU.mul_const _
  have hinner : ∀ t : ℝ, ∫ x, F (x, t) ∂U =
      Complex.exp (-s * (t : ℂ)) * ((∫ x, cdfOf ν (t - x) ∂U : ℝ) : ℂ) := by
    intro t
    simp only [hF]
    rw [integral_const_mul]; congr 1; exact integral_ofReal
  constructor
  · have := hFint.integral_prod_right
    simp_rw [hinner] at this
    exact this
  · unfold twoSidedLaplace
    simp_rw [← hinner]
    have := integral_integral_swap (f := fun x t => F (x, t)) hFint
    rw [← this]
    have h2 : ∀ x : ℝ, ∫ t, F (x, t) = Complex.exp (-(s * (x : ℂ))) * ∫ t, h t := by
      intro x
      simp_rw [hFeq]
      rw [integral_const_mul, integral_sub_right_eq_self h x, neg_mul]
    simp_rw [h2]
    unfold QueueingFundamentals.MG1.lst
    rw [integral_mul_const, mul_comm]

theorem wiener_hopf_core (A B ν : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hν : IsStationaryDelay A B ν) :
    (∀ t : ℝ, negPart (diffLaw A B) (cdfOf ν) t + cdfOf ν t =
        ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B)) ∧
    ∀ s : ℂ, 0 < s.re → Integrable (fun x : ℝ => Real.exp (s.re * x)) A →
      QueueingFundamentals.MG1.lst (diffLaw A B) s = QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ∧
      twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s + twoSidedLaplace (cdfOf ν) s =
        twoSidedLaplace (cdfOf ν) s * (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s) ∧
      (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s ≠ 1 →
        twoSidedLaplace (cdfOf ν) s =
          twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s / (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s - 1)) := by
  obtain ⟨hAp, hA0⟩ := hA
  obtain ⟨hBp, hB0⟩ := hB
  obtain ⟨hνp, hst⟩ := hν
  have := hAp; have := hBp; have := hνp
  haveI : IsProbabilityMeasure (diffLaw A B) := qf_diffLaw_prob A B
  have hneg := qf_stat_neg hst
  refine ⟨fun t => qf_part1 hst t, ?_⟩
  intro s hs hAint
  have hlst := qf_lst_diff A B s
  have hUint := qf_expU_int A B hB0 s.re hs hAint
  obtain ⟨hGint, hGlap⟩ := qf_lap_conv (diffLaw A B) ν hneg s hs hUint
  have hWint := qf_lap_int ν hneg s hs
  have hpt : ∀ t : ℝ, Complex.exp (-s * (t : ℂ)) * (negPart (diffLaw A B) (cdfOf ν) t : ℂ) =
      Complex.exp (-s * (t : ℂ)) * ((∫ x, cdfOf ν (t - x) ∂(diffLaw A B) : ℝ) : ℂ) -
      Complex.exp (-s * (t : ℂ)) * (cdfOf ν t : ℂ) := by
    intro t
    have := qf_part1 hst t
    rw [qf_full_eq_Iic ν _ hneg t] at this
    rw [← this]; push_cast; ring
  have hsum : twoSidedLaplace (negPart (diffLaw A B) (cdfOf ν)) s + twoSidedLaplace (cdfOf ν) s =
      twoSidedLaplace (cdfOf ν) s * (QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s) := by
    rw [← hlst, ← hGlap]
    unfold twoSidedLaplace
    simp_rw [hpt]
    rw [integral_sub hGint hWint]
    ring
  refine ⟨hlst, hsum, fun hne => ?_⟩
  have hne' : QueueingFundamentals.MG1.lst A (-s) * QueueingFundamentals.MG1.lst B s - 1 ≠ 0 :=
    sub_ne_zero.mpr hne
  rw [eq_div_iff hne']
  linear_combination -hsum


section LindleyExist

open ProbabilityTheory Filter Topology

/-- decomposition of the iid product into first coordinate and shift -/
lemma ql_decomp (μ0 : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ0] :
    (Measure.infinitePi (fun _ : ℕ => μ0)).map (fun ω => ((fun j => ω (j + 1)), ω 0)) =
      (Measure.infinitePi (fun _ : ℕ => μ0)).prod μ0 := by
  set P := Measure.infinitePi (fun _ : ℕ => μ0) with hP
  have hind : iIndepFun (fun i (ω : ℕ → ℝ × ℝ) => ω i) P := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ => μ0) (X := fun _ (x : ℝ × ℝ) => x)
      (fun _ => measurable_id)
    exact this
  have hshift : Measurable (fun (ω : ℕ → ℝ × ℝ) j => ω (j + 1)) := by fun_prop
  have hmapshift : P.map (fun ω j => ω (j + 1)) = P := by
    have h2 : iIndepFun (fun j (ω : ℕ → ℝ × ℝ) => ω (j + 1)) P :=
      hind.precomp (g := fun j => j + 1) (fun a b h => by simpa using h)
    rw [h2.map_fun_eq_infinitePi_map (fun j => by fun_prop)]
    congr 1; funext j
    exact Measure.infinitePi_map_eval _ (j + 1)
  have hmap0 : P.map (fun ω => ω 0) = μ0 := Measure.infinitePi_map_eval _ 0
  have hindep : IndepFun (fun (ω : ℕ → ℝ × ℝ) j => ω (j + 1)) (fun ω => ω 0) P := by
    rw [IndepFun_iff_Indep]
    have hI := (iIndepFun_iff_iIndep _ _ _).mp hind
    have h3 := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hI
      (S := ({0}ᶜ : Set ℕ)) (T := ({0} : Set ℕ)) (by simp)
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h3 ?_) ?_
    · show MeasurableSpace.comap (fun (ω : ℕ → ℝ × ℝ) j => ω (j + 1)) MeasurableSpace.pi ≤ _
      rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
      refine iSup_le (fun j => ?_)
      rw [MeasurableSpace.comap_comp]
      exact le_iSup₂_of_le (f := fun i (_ : i ∈ ({0}ᶜ : Set ℕ)) =>
          MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance) (j + 1) (by simp) le_rfl
    · exact le_iSup₂_of_le (f := fun i (_ : i ∈ ({0} : Set ℕ)) =>
          MeasurableSpace.comap (fun ω : ℕ → ℝ × ℝ => ω i) inferInstance) 0 (by simp) le_rfl
  rw [(indepFun_iff_map_prod_eq_prod_map_map hshift.aemeasurable (measurable_pi_apply 0).aemeasurable).mp hindep,
    hmapshift, hmap0]

lemma ql_meanfst (A B : Measure ℝ) [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (hAint : Integrable (fun x : ℝ => x) A) (hBint : Integrable (fun x : ℝ => x) B) :
    ∫ z : ℝ × ℝ, z.1 - z.2 ∂(B.prod A) = meanOf B - meanOf A := by
  have h1 := integral_prod_mul (μ := B) (ν := A) (fun x : ℝ => x) (fun _ : ℝ => (1:ℝ))
  have h2 := integral_prod_mul (μ := B) (ν := A) (fun _ : ℝ => (1:ℝ)) (fun x : ℝ => x)
  simp only [mul_one, one_mul, integral_const, probReal_univ, smul_eq_mul] at h1 h2
  unfold meanOf
  have i1 : Integrable (fun z : ℝ × ℝ => z.1 * (1:ℝ)) (B.prod A) := hBint.mul_prod (integrable_const 1)
  have i2 : Integrable (fun z : ℝ × ℝ => (1:ℝ) * z.2) (B.prod A) := (integrable_const 1).mul_prod hAint
  simp only [mul_one, one_mul] at i1 i2
  rw [integral_sub i1 i2, h1, h2]

lemma ql_bdd (A B : Measure ℝ) [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (hAint : Integrable (fun x : ℝ => x) A) (hBint : Integrable (fun x : ℝ => x) B)
    (hlt : meanOf B < meanOf A) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun _ : ℕ => B.prod A)),
      BddAbove (Set.range (fun n => ∑ i ∈ Finset.range n, ((ω i).1 - (ω i).2))) := by
  set μ0 := B.prod A with hμ0
  set P := Measure.infinitePi (fun _ : ℕ => μ0) with hP
  set g : ℝ × ℝ → ℝ := fun z => z.1 - z.2 with hg
  have hgm : Measurable g := by fun_prop
  have hgint : Integrable g μ0 := by
    have h1 : Integrable (fun z : ℝ × ℝ => z.1 * (1:ℝ)) μ0 := hBint.mul_prod (integrable_const 1)
    have h2 : Integrable (fun z : ℝ × ℝ => (1:ℝ) * z.2) μ0 := (integrable_const 1).mul_prod hAint
    simp only [mul_one, one_mul] at h1 h2
    exact h1.sub h2
  have hmapi : ∀ i, P.map (fun ω => ω i) = μ0 := fun i => Measure.infinitePi_map_eval _ i
  set X : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun i ω => g (ω i) with hX
  have hXmap : ∀ i, P.map (X i) = μ0.map g := by
    intro i
    rw [show X i = g ∘ (fun ω => ω i) from rfl, ← Measure.map_map hgm (measurable_pi_apply i), hmapi]
  have hint : Integrable (X 0) P := by
    have : Integrable g (P.map (fun ω => ω 0)) := by rw [hmapi]; exact hgint
    exact this.comp_measurable (measurable_pi_apply 0)
  have hind : iIndepFun X P :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ0) (X := fun _ => g) (fun _ => hgm)
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
    ⟨(hgm.comp (measurable_pi_apply i)).aemeasurable,
     (hgm.comp (measurable_pi_apply 0)).aemeasurable, by rw [hXmap, hXmap]⟩
  have hslln := strong_law_ae X hint (fun i j hij => hind.indepFun hij) hident
  have hmean : ∫ ω, X 0 ω ∂P = meanOf B - meanOf A := by
    rw [← ql_meanfst A B hAint hBint]
    have := integral_map (μ := P) (measurable_pi_apply 0).aemeasurable (f := g) hgm.aestronglyMeasurable
    rw [hmapi] at this
    exact this.symm
  filter_upwards [hslln] with ω hω
  rw [hmean] at hω
  set m := meanOf B - meanOf A with hm
  have hm0 : m < 0 := by rw [hm]; linarith
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, X i ω) < m / 2 :=
    hω.eventually (gt_mem_nhds (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨∑ k ∈ Finset.range (N + 1), |∑ i ∈ Finset.range k, X i ω|, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hnn : 0 ≤ ∑ k ∈ Finset.range (N + 1), |∑ i ∈ Finset.range k, X i ω| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  by_cases hn : n ≤ N
  · calc (∑ i ∈ Finset.range n, ((ω i).1 - (ω i).2)) ≤ |∑ i ∈ Finset.range n, X i ω| := le_abs_self _
      _ ≤ _ := Finset.single_le_sum (f := fun k => |∑ i ∈ Finset.range k, X i ω|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
  · have h1 := hN n (by omega)
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [smul_eq_mul, inv_mul_lt_iff₀ hnpos] at h1
    have : (n:ℝ) * (m / 2) < 0 := mul_neg_of_pos_of_neg hnpos (by linarith)
    show (∑ i ∈ Finset.range n, X i ω) ≤ _
    linarith

lemma ql_sup_rec (f g : ℕ → ℝ) (c : ℝ) (hf0 : f 0 = 0) (hfs : ∀ n, f (n + 1) = c + g n)
    (hb : BddAbove (Set.range f)) : ⨆ n, f n = max 0 (c + ⨆ n, g n) := by
  have hg : BddAbove (Set.range g) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M - c, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hM ⟨n + 1, rfl⟩
    rw [hfs] at this; linarith
  apply le_antisymm
  · apply ciSup_le
    intro n
    cases n with
    | zero => rw [hf0]; exact le_max_left _ _
    | succ n =>
      rw [hfs]
      exact le_max_of_le_right (by linarith [le_ciSup hg n])
  · apply max_le
    · rw [← hf0]; exact le_ciSup hb 0
    · have : ⨆ n, g n ≤ (⨆ n, f n) - c := by
        apply ciSup_le
        intro n
        have := le_ciSup hb (n + 1)
        rw [hfs] at this; linarith
      linarith

theorem ql_exists (A B : Measure ℝ) [IsProbabilityMeasure A] [IsProbabilityMeasure B]
    (hAint : Integrable (fun x : ℝ => x) A) (hBint : Integrable (fun x : ℝ => x) B)
    (hlt : meanOf B < meanOf A) : ∃ ν : Measure ℝ, IsStationaryDelay A B ν := by
  set μ0 := B.prod A with hμ0
  set P := Measure.infinitePi (fun _ : ℕ => μ0) with hP
  set g : ℝ × ℝ → ℝ := fun z => z.1 - z.2 with hg
  have hgm : Measurable g := by fun_prop
  set S : ℕ → (ℕ → ℝ × ℝ) → ℝ := fun n ω => ∑ i ∈ Finset.range n, ((ω i).1 - (ω i).2) with hS
  set Mx : (ℕ → ℝ × ℝ) → ℝ := fun ω => ⨆ n, S n ω with hMxdef
  have hSm : ∀ n, Measurable (S n) := fun n =>
    Finset.measurable_sum _ (fun i _ => by fun_prop)
  have hMx : Measurable Mx := Measurable.iSup hSm
  refine ⟨P.map Mx, Measure.isProbabilityMeasure_map hMx.aemeasurable, ?_⟩
  have hbdd := ql_bdd A B hAint hBint hlt
  unfold lindleyStep diffLaw
  rw [Measure.map_prod_map P μ0 hMx hgm, ← ql_decomp μ0,
    Measure.map_map (hMx.prodMap hgm) (by fun_prop), Measure.map_map (by fun_prop)
      ((hMx.prodMap hgm).comp (by fun_prop))]
  apply Measure.map_congr
  filter_upwards [hbdd] with ω hω
  simp only [Function.comp, Prod.map]
  have := ql_sup_rec (fun n => S n ω) (fun n => S n (fun j => ω (j + 1))) (g (ω 0))
    (by simp [hS]) (fun n => by
      simp only [hS, hg]
      rw [Finset.sum_range_succ']; ring) hω
  simp only [hMxdef]
  rw [this, add_comm]

end LindleyExist

theorem lindley_core (A B : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hAint : Integrable (fun x : ℝ => x) A) (hBint : Integrable (fun x : ℝ => x) B)
    (hmeanA : 0 < meanOf A) (hρ : trafficIntensity A B < 1) :
    (∃ ν : Measure ℝ, IsStationaryDelay A B ν) ∧
    ∀ ν : Measure ℝ, IsStationaryDelay A B ν →
      ∀ t : ℝ,
        (0 ≤ t →
          cdfOf ν t = ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B) ∧
          cdfOf ν t = ∫ y in Set.Ici 0, cdfOf ν y ∂((diffLaw A B).map (fun x => t - x))) ∧
        (t < 0 → cdfOf ν t = 0) := by
  obtain ⟨hAp, _⟩ := hA
  obtain ⟨hBp, _⟩ := hB
  have hlt : meanOf B < meanOf A := by
    unfold trafficIntensity at hρ
    rwa [div_lt_one hmeanA] at hρ
  refine ⟨ql_exists A B hAint hBint hlt, ?_⟩
  intro ν hν t
  obtain ⟨hνp, hst⟩ := hν
  have : IsProbabilityMeasure (diffLaw A B) := qf_diffLaw_prob A B
  have hneg := qf_stat_neg hst
  refine ⟨fun ht => ?_, fun ht => hneg t ht⟩
  have h1 : cdfOf ν t = ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B) := by
    rw [qf_full_eq_Iic ν _ hneg t]; exact qf_stat_pos hst t ht
  refine ⟨h1, ?_⟩
  rw [setIntegral_map measurableSet_Ici (qf_cdf_meas ν).aestronglyMeasurable (by fun_prop)]
  have hpre : (fun x : ℝ => t - x) ⁻¹' Set.Ici 0 = Set.Iic t := by
    ext x; simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]; constructor <;> intro h <;> linarith
  rw [hpre]; exact h1

end QueueingFundamentals.GG1

open QueueingFundamentals.GG1
open MeasureTheory

theorem solution (A B : Measure ℝ) (hA : IsLifetimeLaw A) (hB : IsLifetimeLaw B)
    (hAint : Integrable (fun x : ℝ => x) A) (hBint : Integrable (fun x : ℝ => x) B)
    (hmeanA : 0 < meanOf A) (hρ : trafficIntensity A B < 1) :
    (∃ ν : Measure ℝ, IsStationaryDelay A B ν) ∧
    ∀ ν : Measure ℝ, IsStationaryDelay A B ν →
      ∀ t : ℝ,
        (0 ≤ t →
          cdfOf ν t = ∫ x in Set.Iic t, cdfOf ν (t - x) ∂(diffLaw A B) ∧
          cdfOf ν t = ∫ y in Set.Ici 0, cdfOf ν y ∂((diffLaw A B).map (fun x => t - x))) ∧
        (t < 0 → cdfOf ν t = 0) := by
  exact lindley_core A B hA hB hAint hBint hmeanA hρ
