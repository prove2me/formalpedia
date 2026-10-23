-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.firstCumulants
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T14:12:53.539987+00:00
-- url     : https://prove2.me/submissions/f687cb1b-7370-487d-b67f-72d4ea22cb90

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

instance X7J_probExp : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

lemma X7J_exp_pos : ∀ᵐ x ∂(expMeasure 1), (0:ℝ) < x := by
  have hf : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [expMeasure, gammaMeasure, ae_withDensity_iff hf]
  have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [hne] with x hx hpdf
  rcases lt_or_gt_of_ne hx with h | h
  · exact absurd (gammaPDF_of_neg h) hpdf
  · exact h

lemma X7J_pi_pos {ι : Type*} [Fintype ι] :
    ∀ᵐ z ∂(Measure.pi fun _ : ι => expMeasure 1), ∀ i, (0:ℝ) < z i :=
  eventually_all.2 fun _ => Measure.tendsto_eval_ae_ae.eventually X7J_exp_pos

lemma X7J_norm_meas {ι : Type*} [Fintype ι] :
    Measurable (normalizePopulation : (ι → ℝ) → (ι → ℝ)) := by
  unfold normalizePopulation
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop

instance X7J_prob {ι : Type*} [Fintype ι] : IsProbabilityMeasure (simplexLaw ι) := by
  unfold simplexLaw
  exact Measure.isProbabilityMeasure_map X7J_norm_meas.aemeasurable

/-- a.e. the simplex law lives in the unit cube. -/
lemma X7J_ae_cube {ι : Type*} [Fintype ι] [Nonempty ι] :
    ∀ᵐ p ∂simplexLaw ι, p ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1) := by
  unfold simplexLaw
  refine (ae_map_iff (p := fun p => p ∈ Set.univ.pi (fun _ : ι => Set.Icc (0:ℝ) 1))
    X7J_norm_meas.aemeasurable
    (isCompact_univ_pi (fun _ => isCompact_Icc)).isClosed.measurableSet).2 ?_
  filter_upwards [X7J_pi_pos] with z hz
  have hS : 0 < ∑ i, z i := Finset.sum_pos (fun i _ => hz i) Finset.univ_nonempty
  simp only [normalizePopulation, hS.ne', if_false]
  intro i _
  refine ⟨div_nonneg (hz i).le hS.le, (div_le_one hS).2 ?_⟩
  exact Finset.single_le_sum (fun j _ => (hz j).le) (Finset.mem_univ i)

lemma X7J_cont {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    Continuous (generated (conjSuperop U)) := by
  unfold generated coherence conjSuperop inputDensity
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact continuous_const
  · refine Complex.continuous_normSq.comp ?_
    simp only [Matrix.mul_apply, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    fun_prop

lemma X7J_bdd {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) :
    ∃ C, ∀ᵐ p ∂simplexLaw ι, |generated (conjSuperop U) p| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ_pi (fun _ : ι => isCompact_Icc (a := (0:ℝ)) (b := 1))).exists_bound_of_continuousOn
    (X7J_cont U).continuousOn
  refine ⟨C, ?_⟩
  filter_upwards [X7J_ae_cube] with p hp
  exact hC p hp

lemma X7J_int {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) (t : ℝ) :
    Integrable (fun p => Real.exp (t * generated (conjSuperop U) p)) (simplexLaw ι) := by
  obtain ⟨C, hC⟩ := X7J_bdd U
  refine Integrable.of_bound (C := Real.exp (|t| * C)) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul (X7J_cont U))).aestronglyMeasurable
  · filter_upwards [hC] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    calc t * generated (conjSuperop U) p ≤ |t * generated (conjSuperop U) p| := le_abs_self _
      _ = |t| * |generated (conjSuperop U) p| := abs_mul _ _
      _ ≤ |t| * C := mul_le_mul_of_nonneg_left hp (abs_nonneg _)

lemma X7J_interior {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) (t : ℝ) :
    t ∈ interior (integrableExpSet (generated (conjSuperop U)) (simplexLaw ι)) := by
  have : integrableExpSet (generated (conjSuperop U)) (simplexLaw ι) = Set.univ := by
    ext s; simp only [Set.mem_univ, iff_true]; exact X7J_int U s
  rw [this, interior_univ]; trivial

lemma X7J_cumulant {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) :
    cumulant (conjSuperop U) = cgf (generated (conjSuperop U)) (simplexLaw ι) := rfl

lemma X7J_deriv0 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) :
    deriv (cumulant (conjSuperop U)) 0 = cgp (conjSuperop U) := by
  rw [X7J_cumulant, deriv_cgf_zero (X7J_interior U 0)]
  simp [cgp, moment]

lemma X7J_deriv2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ) :
    HasDerivAt (deriv (cumulant (conjSuperop U))) (cgpd (conjSuperop U) ^ 2) 0 := by
  have hA := analyticAt_cgf (X7J_interior U 0)
  have hd : DifferentiableAt ℝ (deriv (cumulant (conjSuperop U))) 0 := by
    rw [X7J_cumulant]; exact hA.deriv.differentiableAt
  suffices hv : deriv (deriv (cumulant (conjSuperop U))) 0 = cgpd (conjSuperop U) ^ 2 by
    rw [← hv]; exact hd.hasDerivAt
  have h2 := iteratedDeriv_two_cgf_eq_integral (X7J_interior U 0)
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
  rw [X7J_cumulant, h2, ← X7J_cumulant, X7J_deriv0]
  simp only [zero_mul, Real.exp_zero, mul_one, mgf_zero, probReal_univ, div_one]
  rw [cgpd, Real.sq_sqrt]
  · rfl
  · exact integral_nonneg fun p => sq_nonneg _

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (U : Matrix ι ι ℂ)
    (hU : U ∈ Matrix.unitaryGroup ι ℂ) :
    (∀ a : ℝ, 0 < partition (conjSuperop U) a) ∧
    HasDerivAt (cumulant (conjSuperop U)) (cgp (conjSuperop U)) 0 ∧
    HasDerivAt (deriv (cumulant (conjSuperop U))) (cgpd (conjSuperop U) ^ 2) 0 := by
  refine ⟨fun a => mgf_pos (X7J_int U a), ?_, X7J_deriv2 U⟩
  rw [← X7J_deriv0]
  rw [X7J_cumulant]
  exact (analyticAt_cgf (X7J_interior U 0)).differentiableAt.hasDerivAt
