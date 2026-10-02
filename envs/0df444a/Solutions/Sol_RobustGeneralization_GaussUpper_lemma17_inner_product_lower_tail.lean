-- Prove2me | solution 1 for RobustGeneralization.GaussUpper.lemma17_inner_product_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:41:44.886815+00:00
-- url     : https://prove2.me/submissions/5d03ced3-e84b-42e2-b360-ff7462b1bc9a

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem rg17_mgf1 (s : ℝ) :
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

theorem rg17_pi_lint {ι X : Type*} [Fintype ι] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ S, ∏ i, f i (S i) ∂(Measure.pi fun _ : ι => ν) = ∏ i, ∫⁻ x, f i x ∂ν := by
  have hind : iIndepFun (fun i (S : ι → X) => f i (S i)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi (X := fun i => f i) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : ι => ν) i).lintegral_comp (hf i)

theorem rg17_mgfE {d : ℕ} (h : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
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
  rw [rg17_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp ((t * h i) * x)))
    (fun i => by fun_prop)]
  simp_rw [rg17_mgf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring


theorem rg17_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
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
theorem solution (d : ℕ) (μ : E d) (σ : ℝ) (hσ : 0 < σ) (w : E d)
    (hw : ‖w‖ = 1) (ρ : ℝ) (hρ : 0 ≤ ρ) (hwμ : ρ ≤ inner ℝ w μ) :
    gaussVec μ σ {z | inner ℝ w z ≤ ρ} ≤
      ENNReal.ofReal (Real.exp (-(inner ℝ w μ - ρ) ^ 2 / (2 * σ ^ 2))) := by
  set δ : ℝ := inner ℝ w μ - ρ with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  set t : ℝ := -δ / σ with ht
  unfold gaussVec
  rw [Measure.map_apply (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)]
  have hsub : (fun v : E d => μ + σ • v) ⁻¹' {z | inner ℝ w z ≤ ρ} ⊆
      {v | δ ^ 2 / σ ^ 2 ≤ t * inner ℝ w v} := by
    intro v hv
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, inner_add_right, real_inner_smul_right] at hv ⊢
    have h1 : σ * inner ℝ w v ≤ -δ := by rw [hδ]; linarith
    have h2 : δ / σ ^ 2 * (σ * inner ℝ w v) ≤ δ / σ ^ 2 * (-δ) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have e1 : δ / σ ^ 2 * (σ * inner ℝ w v) = - (t * inner ℝ w v) := by
      rw [ht]; field_simp
    have e2 : δ / σ ^ 2 * (-δ) = - (δ ^ 2 / σ ^ 2) := by ring
    linarith
  calc stdGaussian (E d) ((fun v : E d => μ + σ • v) ⁻¹' {z | inner ℝ w z ≤ ρ})
      ≤ stdGaussian (E d) {v | δ ^ 2 / σ ^ 2 ≤ t * inner ℝ w v} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(δ ^ 2 / σ ^ 2))) *
          ∫⁻ v, ENNReal.ofReal (Real.exp (t * inner ℝ w v)) ∂(stdGaussian (E d)) :=
        rg17_markov _ _ (by fun_prop) _
    _ = ENNReal.ofReal (Real.exp (-(inner ℝ w μ - ρ) ^ 2 / (2 * σ ^ 2))) := by
        rw [rg17_mgfE, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [hw, ht, ← hδ]
        field_simp
        ring
