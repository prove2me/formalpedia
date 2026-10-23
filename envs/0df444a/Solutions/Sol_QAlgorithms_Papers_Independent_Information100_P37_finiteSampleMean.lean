-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.finiteSampleMean
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T13:17:09.93398+00:00
-- url     : https://prove2.me/submissions/b000b606-deac-4403-918d-8b0f7ca7a12c

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

lemma X7S_int_pi {ι : Type*} [Fintype ι] (N : ℕ) (F : (Fin N → ι → ℝ) → ℝ) (hF : Continuous F) :
    Integrable F (sampleLaw ι N) := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi fun _ : Fin N =>
    isCompact_univ_pi fun _ : ι => isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hF.continuousOn
  unfold sampleLaw
  refine Integrable.of_bound hF.aestronglyMeasurable C ?_
  have : ∀ᵐ P ∂(Measure.pi fun _ : Fin N => simplexLaw ι), ∀ k,
      P k ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1) :=
    eventually_all.2 fun _ => Measure.tendsto_eval_ae_ae.eventually X7S_ae_simplex
  filter_upwards [this] with P hP
  exact hC P fun k _ => hP k

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) (N : ℕ) (hN : 1 ≤ N) :
    let E := conjSuperop U
    (∫ p, empiricalMean E p ∂sampleLaw ι N) = cgp E ∧
    (∫ p, (empiricalMean E p - cgp E) ^ 2 ∂sampleLaw ι N) = cgpd E ^ 2 / (N : ℝ) ∧
    (∀ e : ℝ, 0 < e →
      (Real.sqrt (∫ p, (empiricalMean E p - cgp E) ^ 2 ∂sampleLaw ι N) ≤ e ↔
        cgpd E ^ 2 / e ^ 2 ≤ (N : ℝ))) := by
  intro E
  set X := generated E with hXdef
  set c := cgp E with hcdef
  have hXc : Continuous X := X7S_gen_cont U
  have hXi : Integrable X (simplexLaw ι) := X7S_int X hXc
  have hc : ∫ p, X p ∂simplexLaw ι = c := by
    simp [hcdef, cgp, QAlgorithms.Papers.Independent.Information100.P37.moment, hXdef]
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := hNpos.ne'
  have hcomp : ∀ (g : (ι → ℝ) → ℝ), Continuous g → ∀ i : Fin N,
      ∫ P, g (P i) ∂sampleLaw ι N = ∫ p, g p ∂simplexLaw ι := fun g hg i => by
    unfold sampleLaw
    exact integral_comp_eval hg.aestronglyMeasurable
  -- the mean
  have h1 : (∫ P, empiricalMean E P ∂sampleLaw ι N) = c := by
    simp only [empiricalMean, ← hXdef]
    rw [integral_div, integral_finsetSum _ fun i _ =>
      X7S_int_pi N (fun P => X (P i)) (hXc.comp (continuous_apply i))]
    simp only [fun i => hcomp X hXc i, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  -- the variance
  set v := coherenceVariance E with hvdef
  have hv : ∫ p, (X p - c) ^ 2 ∂simplexLaw ι = v := by simp [hvdef, coherenceVariance, hXdef, hcdef]
  have hv0 : 0 ≤ v := by rw [← hv]; exact integral_nonneg fun _ => sq_nonneg _
  have hcgpd : cgpd E ^ 2 = v := by rw [cgpd, Real.sq_sqrt hv0]
  have hY0 : ∫ p, (X p - c) ∂simplexLaw ι = 0 := by
    rw [integral_sub hXi (integrable_const c), hc]; simp
  have hYc : Continuous fun p => X p - c := hXc.sub continuous_const
  have hpair : ∀ i j : Fin N, ∫ P, (X (P i) - c) * (X (P j) - c) ∂sampleLaw ι N =
      if i = j then v else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      simp_rw [← sq]
      rw [hcomp (fun p => (X p - c) ^ 2) (hYc.pow 2) i, hv]
    · let g : Fin N → (ι → ℝ) → ℝ := fun k p => if k = i then X p - c else if k = j then X p - c else 1
      have hprod : ∀ P : Fin N → ι → ℝ, (X (P i) - c) * (X (P j) - c) = ∏ k, g k (P k) := by
        intro P
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
          ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
        rw [Finset.prod_eq_one]
        · simp [g, Ne.symm hij]
        · intro k hk
          simp only [Finset.mem_erase] at hk
          simp [g, hk.1, hk.2.1]
      simp_rw [hprod]
      unfold sampleLaw
      rw [integral_fintype_prod_eq_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [g, hY0])
  have hexp : ∀ P : Fin N → ι → ℝ, (empiricalMean E P - c) ^ 2 =
      (∑ i, ∑ j, (X (P i) - c) * (X (P j) - c)) / (N : ℝ) ^ 2 := by
    intro P
    simp only [empiricalMean, ← hXdef]
    rw [← Finset.sum_mul_sum, ← sq, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h2 : (∫ P, (empiricalMean E P - c) ^ 2 ∂sampleLaw ι N) = v / N := by
    simp_rw [hexp]
    rw [integral_div, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      X7S_int_pi N (fun P => (X (P i) - c) * (X (P j) - c))
        ((hYc.comp (continuous_apply i)).mul (hYc.comp (continuous_apply j)))]
    have hin : ∀ i : Fin N, ∫ P, ∑ j, (X (P i) - c) * (X (P j) - c) ∂sampleLaw ι N =
        ∑ j, ∫ P, (X (P i) - c) * (X (P j) - c) ∂sampleLaw ι N := fun i =>
      integral_finsetSum _ fun j _ => X7S_int_pi N (fun P => (X (P i) - c) * (X (P j) - c))
        ((hYc.comp (continuous_apply i)).mul (hYc.comp (continuous_apply j)))
    simp only [hin]
    simp only [hpair, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨h1, by rw [h2, hcgpd], fun e he => ?_⟩
  rw [h2, hcgpd, Real.sqrt_le_left he.le, div_le_iff₀ hNpos, div_le_iff₀ (by positivity),
    mul_comm]
