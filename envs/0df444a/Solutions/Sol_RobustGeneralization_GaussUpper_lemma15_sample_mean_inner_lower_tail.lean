-- Prove2me | solution 1 for RobustGeneralization.GaussUpper.lemma15_sample_mean_inner_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:35:45.622931+00:00
-- url     : https://prove2.me/submissions/f4c41ed0-9dcd-49cb-b850-52570d13c787

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem rg15_mgf1 (s : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (s * x)) ∂(gaussianReal 0 1)
      = ENNReal.ofReal (Real.exp (s ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal s)
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  congr 1
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) s
  simp only [mgf, id] at h
  rw [h]
  congr 1
  push_cast
  ring

theorem rg15_pi_lint {ι X : Type*} [Fintype ι] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ S, ∏ i, f i (S i) ∂(Measure.pi fun _ : ι => ν) = ∏ i, ∫⁻ x, f i x ∂ν := by
  have hind : iIndepFun (fun i (S : ι → X) => f i (S i)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi (X := fun i => f i) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : ι => ν) i).lintegral_comp (hf i)

theorem rg15_mgfE {d : ℕ} (h : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (t * inner ℝ h v)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ENNReal.ofReal (Real.exp (t ^ 2 * ‖h‖ ^ 2 / 2)) := by
  rw [← map_pi_eq_stdGaussian, lintegral_map (by fun_prop) (by fun_prop)]
  have hprod : ∀ x : Fin d → ℝ,
      ENNReal.ofReal (Real.exp (t * inner ℝ h (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))))
      = ∏ i, ENNReal.ofReal (Real.exp ((t * h i) * x i)) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
    congr 2
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  simp_rw [hprod]
  rw [rg15_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp ((t * h i) * x)))
    (fun i => by fun_prop)]
  simp_rw [rg15_mgf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring


theorem rg15_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
    (hg : Measurable g) (a : ℝ) :
    μ {x | a ≤ g x} ≤ ENNReal.ofReal (Real.exp (-a)) * ∫⁻ x, ENNReal.ofReal (Real.exp (g x)) ∂μ := by
  have h1 := mul_meas_ge_le_lintegral₀ (μ := μ) (f := fun x => ENNReal.ofReal (Real.exp (g x)))
    (Real.measurable_exp.comp hg).ennreal_ofReal.aemeasurable (ENNReal.ofReal (Real.exp a))
  have hsub : {x | a ≤ g x} ⊆
      {x | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (g x))} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hx)
  calc μ {x | a ≤ g x}
      ≤ μ {x | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (g x))} := measure_mono hsub
    _ = ENNReal.ofReal (Real.exp (-a)) * (ENNReal.ofReal (Real.exp a) *
          μ {x | ENNReal.ofReal (Real.exp a) ≤ ENNReal.ofReal (Real.exp (g x))}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        simp
    _ ≤ _ := by gcongr


open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem rg15_prob {d : ℕ} (m : E d) (s : ℝ) : IsProbabilityMeasure (gaussVec m s) := by
  unfold gaussVec
  exact Measure.isProbabilityMeasure_map (by fun_prop)

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem rg15_mgf {d : ℕ} (μ : E d) (σ s : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (s * inner ℝ z μ)) ∂(gaussVec μ σ)
      = ENNReal.ofReal (Real.exp (s * ‖μ‖ ^ 2 + (s * σ) ^ 2 * ‖μ‖ ^ 2 / 2)) := by
  unfold gaussVec
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  have h : ∀ v : E d, ENNReal.ofReal (Real.exp (s * inner ℝ (μ + σ • v) μ))
      = ENNReal.ofReal (Real.exp (s * ‖μ‖ ^ 2)) *
          ENNReal.ofReal (Real.exp ((s * σ) * inner ℝ μ v)) := by
    intro v
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm]
    ring
  simp_rw [h]
  rw [lintegral_const_mul _ (by fun_prop), rg15_mgfE, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem solution (d n : ℕ) (hn : 1 ≤ n) (μ : E d) (hμ : μ ≠ 0)
    (σ : ℝ) (hσ : 0 < σ) (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | inner ℝ (zbar' z) μ ≤
          ‖μ‖ ^ 2 - σ * ‖μ‖ * Real.sqrt (2 * Real.log (1 / δ) / n)} ≤
      ENNReal.ofReal δ := by
  have : IsProbabilityMeasure (gaussVec μ σ) := rg15_prob μ σ
  rcases le_or_gt 1 δ with h1 | h1
  · calc _ ≤ (1 : ℝ≥0∞) := prob_le_one
      _ ≤ ENNReal.ofReal δ := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1
  set L : ℝ := Real.log (1 / δ) with hL
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos; rw [one_div]; exact one_lt_inv₀ hδ |>.2 h1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set r : ℝ := Real.sqrt (2 * L / n) with hr
  have hr2 : r ^ 2 = 2 * L / n := Real.sq_sqrt (by positivity)
  have hnr : (n : ℝ) * r ^ 2 = 2 * L := by rw [hr2]; field_simp
  set m : ℝ := ‖μ‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 hμ
  set s : ℝ := -r / (σ * m) with hs
  have hs0 : s ≤ 0 := by
    rw [hs]; apply div_nonpos_of_nonpos_of_nonneg
    · have : 0 ≤ r := Real.sqrt_nonneg _
      linarith
    · positivity
  have hinner : ∀ z : Fin n → E d, inner ℝ (zbar' z) μ = (n : ℝ)⁻¹ * ∑ i, inner ℝ (z i) μ := by
    intro z
    unfold zbar'
    rw [real_inner_smul_left, sum_inner]
  set g : (Fin n → E d) → ℝ := fun z => ∑ i, s * inner ℝ (z i) μ with hg
  have hgm : Measurable g := by rw [hg]; fun_prop
  set a : ℝ := s * n * (m ^ 2 - σ * m * r) with ha
  have hsub : {z : Fin n → E d | inner ℝ (zbar' z) μ ≤ m ^ 2 - σ * m * r} ⊆ {z | a ≤ g z} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    rw [hinner] at hz
    have h2 : ∑ i, inner ℝ (z i) μ ≤ n * (m ^ 2 - σ * m * r) := by
      have := mul_le_mul_of_nonneg_left hz hnR.le
      rw [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul] at this
      exact this
    have h3 := mul_le_mul_of_nonpos_left h2 hs0
    rw [hg, ha]
    simp only
    rw [← Finset.mul_sum]
    linarith
  calc _ ≤ (Measure.pi fun _ : Fin n => gaussVec μ σ) {z | a ≤ g z} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-a)) *
          ∫⁻ z, ENNReal.ofReal (Real.exp (g z)) ∂(Measure.pi fun _ : Fin n => gaussVec μ σ) :=
        rg15_markov _ _ hgm _
    _ = ENNReal.ofReal (Real.exp (-a)) *
          ∏ _i : Fin n, ENNReal.ofReal (Real.exp (s * m ^ 2 + (s * σ) ^ 2 * m ^ 2 / 2)) := by
        congr 1
        have hp : ∀ z : Fin n → E d, ENNReal.ofReal (Real.exp (g z))
            = ∏ i, ENNReal.ofReal (Real.exp (s * inner ℝ (z i) μ)) := by
          intro z
          rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
        simp_rw [hp]
        rw [rg15_pi_lint (gaussVec μ σ) (fun _ z => ENNReal.ofReal (Real.exp (s * inner ℝ z μ)))
          (fun _ => by fun_prop)]
        simp_rw [rg15_mgf, hm]
    _ = ENNReal.ofReal (Real.exp (-L)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow
          (Real.exp_pos _).le, ← Real.exp_nat_mul, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← Real.exp_add]
        congr 2
        rw [ha, hs]
        field_simp
        linear_combination (-σ) * hnr
    _ = ENNReal.ofReal δ := by
        rw [hL, one_div, Real.log_inv, neg_neg, Real.exp_log hδ]
