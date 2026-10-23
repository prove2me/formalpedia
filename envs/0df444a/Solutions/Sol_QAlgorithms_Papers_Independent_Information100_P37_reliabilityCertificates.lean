-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.reliabilityCertificates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:25:25.242287+00:00
-- url     : https://prove2.me/submissions/5761d613-cd50-4892-95f7-83910b1a36cd

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

open scoped BigOperators Matrix ComplexConjugate Topology ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P37

instance X7S_probExp : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos

lemma X7S_exp_pos : ∀ᵐ x ∂(expMeasure 1), (0:ℝ) < x := by
  have hf : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, ae_withDensity_iff hf]
  have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [hne] with x hx hpdf
  rcases lt_or_gt_of_ne hx with h | h
  · exact absurd (gammaPDF_of_neg h) hpdf
  · exact h

lemma X7S_pi_pos {ι : Type*} [Fintype ι] :
    ∀ᵐ z ∂(Measure.pi fun _ : ι => expMeasure 1), ∀ i, (0:ℝ) < z i :=
  eventually_all.2 fun _ => Measure.tendsto_eval_ae_ae.eventually X7S_exp_pos

lemma X7S_norm_meas {ι : Type*} [Fintype ι] :
    Measurable (normalizePopulation : (ι → ℝ) → (ι → ℝ)) := by
  unfold normalizePopulation
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop

instance X7S_prob {ι : Type*} [Fintype ι] : IsProbabilityMeasure (simplexLaw ι) := by
  unfold simplexLaw
  exact Measure.isProbabilityMeasure_map X7S_norm_meas.aemeasurable

lemma X7S_ae_simplex {ι : Type*} [Fintype ι] :
    ∀ᵐ p ∂(simplexLaw ι), p ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1) := by
  unfold simplexLaw
  have hs : MeasurableSet {y : ι → ℝ | y ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1)} :=
    (isClosed_set_pi fun _ _ => isClosed_Icc).measurableSet
  refine (ae_map_iff X7S_norm_meas.aemeasurable hs).mpr ?_
  filter_upwards [X7S_pi_pos] with z hz
  intro i _
  have hcard : (1:ℝ) ≤ Fintype.card ι := by
    have := Fintype.card_pos_iff.mpr ⟨i⟩; exact_mod_cast this
  unfold normalizePopulation
  split_ifs with h0
  · exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact hcard⟩
  · have hS : 0 < ∑ j, z j := Finset.sum_pos (fun j _ => hz j) ⟨i, Finset.mem_univ i⟩
    refine ⟨div_nonneg (hz i).le hS.le, (div_le_one hS).mpr ?_⟩
    exact Finset.single_le_sum (fun j _ => (hz j).le) (Finset.mem_univ i)

/-- Every continuous function is integrable for the simplex law (compact support). -/
lemma X7S_int {ι : Type*} [Fintype ι] (f : (ι → ℝ) → ℝ) (hf : Continuous f) :
    Integrable f (simplexLaw ι) := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ : ι => isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [X7S_ae_simplex] with p hp
  exact hC p hp

lemma X7S_gen_cont {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    Continuous (generated (conjSuperop U)) := by
  have h : ∀ p : ι → ℝ, generated (conjSuperop U) p = ∑ i, ∑ j, if i = j then 0 else
      Complex.normSq (∑ k, U i k * (p k : ℂ) * star (U j k)) := by
    intro p
    simp only [generated, coherence, conjSuperop, inputDensity, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Finset.sum_ite_eq', mul_ite]
  simp_rw [funext h]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  split_ifs
  · exact continuous_const
  · exact Complex.continuous_normSq.comp (continuous_finset_sum _ fun k _ => by fun_prop)

lemma X7R_markov {ι : Type*} [Fintype ι] (X : (ι → ℝ) → ℝ) (hX : Continuous X) (c v : ℝ)
    (hc : ∫ p, X p ∂simplexLaw ι = c) (hv : ∫ p, (X p - c) ^ 2 ∂simplexLaw ι = v) (t : ℝ) :
    ∫ p, (c - X p + t) ^ 2 ∂simplexLaw ι = v + t ^ 2 := by
  have h : ∀ p, (c - X p + t) ^ 2 = ((X p - c) ^ 2 + (-2 * t) * (X p - c)) + t ^ 2 := fun p => by ring
  simp_rw [h]
  have i1 : Integrable (fun p => (X p - c) ^ 2) (simplexLaw ι) := X7S_int _ (by fun_prop)
  have i2 : Integrable (fun p => X p - c) (simplexLaw ι) := X7S_int _ (by fun_prop)
  have i3 : Integrable (fun p => (X p - c) ^ 2 + -2 * t * (X p - c)) (simplexLaw ι) :=
    i1.add (i2.const_mul _)
  have i4 : Integrable (fun p => -2 * t * (X p - c)) (simplexLaw ι) := i2.const_mul _
  rw [integral_add i3 (integrable_const _), integral_add i1 i4,
    integral_const_mul, integral_sub (X7S_int _ hX) (integrable_const _), hc, hv]
  simp

lemma X7R_cantelli {ι : Type*} [Fintype ι] (X : (ι → ℝ) → ℝ) (hX : Continuous X) (c v e : ℝ)
    (hc : ∫ p, X p ∂simplexLaw ι = c) (hv : ∫ p, (X p - c) ^ 2 ∂simplexLaw ι = v) (he : 0 < e) :
    (simplexLaw ι).real {p | X p ≤ c - e} ≤ v / (v + e ^ 2) := by
  have hv0 : 0 ≤ v := by rw [← hv]; exact integral_nonneg fun _ => sq_nonneg _
  set t := v / e with ht
  have ht0 : 0 ≤ t := div_nonneg hv0 he.le
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := simplexLaw ι)
    (f := fun p => (c - X p + t) ^ 2) (Eventually.of_forall fun _ => sq_nonneg _)
    (X7S_int _ (by fun_prop)) ((e + t) ^ 2)
  rw [X7R_markov X hX c v hc hv t] at hm
  have hsub : {p | X p ≤ c - e} ⊆ {p | (e + t) ^ 2 ≤ (c - X p + t) ^ 2} := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp ⊢
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hpos : 0 < (e + t) ^ 2 := by positivity
  calc (simplexLaw ι).real {p | X p ≤ c - e}
      ≤ (simplexLaw ι).real {p | (e + t) ^ 2 ≤ (c - X p + t) ^ 2} := measureReal_mono hsub
    _ ≤ (v + t ^ 2) / (e + t) ^ 2 := by rw [le_div_iff₀ hpos]; linarith
    _ = v / (v + e ^ 2) := by
      rw [ht]; field_simp; ring

lemma X7R_cheb {ι : Type*} [Fintype ι] (X : (ι → ℝ) → ℝ) (hX : Continuous X) (c v e : ℝ)
    (hv : ∫ p, (X p - c) ^ 2 ∂simplexLaw ι = v) (he : 0 < e) :
    (simplexLaw ι).real {p | |X p - c| ≥ e} ≤ v / e ^ 2 := by
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := simplexLaw ι)
    (f := fun p => (X p - c) ^ 2) (Eventually.of_forall fun _ => sq_nonneg _)
    (X7S_int _ (by fun_prop)) (e ^ 2)
  rw [hv] at hm
  have hset : {p | |X p - c| ≥ e} = {p | e ^ 2 ≤ (X p - c) ^ 2} := by
    ext p; simp only [Set.mem_ofPred_eq, ge_iff_le]
    rw [← sq_abs (X p - c)]
    exact (pow_le_pow_iff_left₀ he.le (abs_nonneg _) two_ne_zero).symm
  rw [hset, le_div_iff₀ (by positivity)]; linarith

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (e : ℝ) (he : 0 < e) :
    let E := conjSuperop U
    (simplexLaw ι).real {p | generated E p ≤ cgp E - e} ≤ cgpd E ^ 2 / (cgpd E ^ 2 + e ^ 2) ∧
    (simplexLaw ι).real {p | |generated E p - cgp E| ≥ e} ≤ cgpd E ^ 2 / e ^ 2 ∧
    (∀ a : ℝ, 0 < a → a < 1 →
      1 - a ≤ (simplexLaw ι).real {p | max 0 (cgp E - Real.sqrt ((1 - a) / a) * cgpd E) ≤ generated E p}) := by
  intro E
  set X := generated E with hXdef
  set c := cgp E with hcdef
  have hXc : Continuous X := X7S_gen_cont U
  have hc : ∫ p, X p ∂simplexLaw ι = c := by
    simp [hcdef, cgp, QAlgorithms.Papers.Independent.Information100.P37.moment, hXdef]
  set v := coherenceVariance E with hvdef
  have hv : ∫ p, (X p - c) ^ 2 ∂simplexLaw ι = v := by simp [hvdef, coherenceVariance, hXdef, hcdef]
  have hv0 : 0 ≤ v := by rw [← hv]; exact integral_nonneg fun _ => sq_nonneg _
  have hcgpd : cgpd E ^ 2 = v := by rw [cgpd, Real.sq_sqrt hv0]
  have hX0 : ∀ p, 0 ≤ X p := fun p => by
    simp only [hXdef, generated, coherence]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact le_rfl
      · exact Complex.normSq_nonneg _
  rw [hcgpd]
  refine ⟨X7R_cantelli X hXc c v e hc hv he, X7R_cheb X hXc c v e hv he, fun a ha0 ha1 => ?_⟩
  set k := Real.sqrt ((1 - a) / a) with hk
  set m := max 0 (c - k * cgpd E) with hm
  have hS : MeasurableSet {p | m ≤ X p} := measurableSet_le measurable_const hXc.measurable
  have hsum := measureReal_add_measureReal_compl (μ := simplexLaw ι) hS
  simp only [probReal_univ] at hsum
  have hcompl : {p | m ≤ X p}ᶜ = {p | X p < m} := by ext p; simp
  rw [hcompl] at hsum
  suffices hsa : (simplexLaw ι).real {p | X p < m} ≤ a by linarith
  rcases le_or_gt (c - k * cgpd E) 0 with h0 | h0
  · have : {p | X p < m} = ∅ := by
      ext p; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, hm,
        max_eq_left h0]
      exact hX0 p
    rw [this]; simp; exact ha0.le
  · have hmc : m = c - k * cgpd E := by rw [hm, max_eq_right h0.le]
    rcases eq_or_lt_of_le (Real.sqrt_nonneg v) with hs | hs
    · -- zero variance: X = c almost everywhere
      have hv' : v = 0 := by
        have := Real.sqrt_eq_zero'.mp hs.symm; linarith
      have hσ : cgpd E = 0 := by rw [cgpd, ← hvdef, hv']; simp
      rw [hmc, hσ, mul_zero, sub_zero]
      have hae : (fun p => (X p - c) ^ 2) =ᵐ[simplexLaw ι] 0 := by
        have hi : Integrable (fun p => (X p - c) ^ 2) (simplexLaw ι) :=
          X7S_int _ ((hXc.sub continuous_const).pow 2)
        refine (integral_eq_zero_iff_of_nonneg (fun p => sq_nonneg (X p - c)) hi).mp ?_
        rw [hv, hv']
      have hnull : simplexLaw ι {p | X p < c} = 0 := by
        refine measure_mono_null ?_ (ae_iff.mp hae)
        intro p hp
        simp only [Set.mem_ofPred_eq, Pi.zero_apply] at hp ⊢
        exact pow_ne_zero 2 (sub_ne_zero.mpr hp.ne)
      rw [measureReal_def, hnull]; simp; exact ha0.le
    · have hσ : 0 < cgpd E := by rw [cgpd, ← hvdef]; exact hs
      have hk0 : 0 < k := Real.sqrt_pos.mpr (div_pos (by linarith) ha0)
      have hepos : 0 < k * cgpd E := mul_pos hk0 hσ
      have hsub : {p | X p < m} ⊆ {p | X p ≤ c - k * cgpd E} := by
        intro p hp; simp only [Set.mem_ofPred_eq] at hp ⊢; rw [hmc] at hp; exact hp.le
      refine (measureReal_mono hsub).trans ((X7R_cantelli X hXc c v _ hc hv hepos).trans ?_)
      have hk2 : k ^ 2 = (1 - a) / a := Real.sq_sqrt (div_nonneg (by linarith) ha0.le)
      have hvpos : 0 < v := by rw [← hcgpd]; positivity
      rw [mul_pow, hk2, hcgpd, div_le_iff₀ (by positivity)]
      field_simp
      ring_nf
      nlinarith
