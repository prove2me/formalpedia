-- Prove2me | solution 1 for RobustGeneralization.GaussUpper.lemma16_normalized_mean_inner_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:52:20.283421+00:00
-- url     : https://prove2.me/submissions/5fd9f3bd-3b15-4ac1-a461-a2f12efe7542

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem l16_mgf1 (s : ℝ) :
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

theorem l16_pi_lint {ι X : Type*} [Fintype ι] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ S, ∏ i, f i (S i) ∂(Measure.pi fun _ : ι => ν) = ∏ i, ∫⁻ x, f i x ∂ν := by
  have hind : iIndepFun (fun i (S : ι → X) => f i (S i)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi (X := fun i => f i) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : ι => ν) i).lintegral_comp (hf i)

theorem l16_mgfE {d : ℕ} (h : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
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
  rw [l16_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp ((t * h i) * x)))
    (fun i => by fun_prop)]
  simp_rw [l16_mgf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

theorem l16_gauss_sq_int (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) ∧
      ∫ x, Real.exp (t * x ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hb : 0 < 1 / 2 - t := by linarith
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal, mul_assoc, ← Real.exp_add]
    congr 2
    · simp
    · push_cast; ring
  constructor
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
        (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))]
    have : (fun x : ℝ => (gaussianPDF 0 1 x).toReal • Real.exp (t * x ^ 2))
        = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * x ^ 2) := by
      funext x
      rw [toReal_gaussianPDF, smul_eq_mul, hpt]
    rw [this]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp_rw [smul_eq_mul, hpt]
    rw [integral_const_mul, integral_gaussian]
    have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
    have h3 : (0 : ℝ) < 1 - 2 * t := by linarith
    rw [show Real.pi / (1 / 2 - t) = (2 * Real.pi) / (1 - 2 * t) by field_simp]
    rw [Real.sqrt_div h2.le, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.2 h2).ne', one_mul]

theorem l16_sq1 :
    ∫⁻ x, ENNReal.ofReal (Real.exp ((1 / 4) * x ^ 2)) ∂(gaussianReal 0 1)
      ≤ ENNReal.ofReal (Real.exp (3 / 8)) := by
  obtain ⟨hi, he⟩ := l16_gauss_sq_int (1 / 4) (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)), he]
  apply ENNReal.ofReal_le_ofReal
  -- (√(1/2))⁻¹ = √2 ≤ exp(3/8)
  have h1 : (Real.sqrt (1 - 2 * (1 / 4 : ℝ)))⁻¹ = Real.sqrt 2 := by
    rw [show (1 - 2 * (1 / 4 : ℝ)) = (Real.sqrt 2)⁻¹ ^ 2 by
      rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num]
    rw [Real.sqrt_sq (by positivity), inv_inv]
  rw [h1]
  have h2 : Real.sqrt 2 < 1.415 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3 : (1.415 : ℝ) ≤ Real.exp (3 / 8) := by
    have := Real.add_one_le_exp (3 / 8 : ℝ)
    have h4 := Real.quadratic_le_exp_of_nonneg (show (0:ℝ) ≤ 3 / 8 by norm_num)
    nlinarith
  linarith

theorem l16_sqE {d : ℕ} :
    ∫⁻ v, ENNReal.ofReal (Real.exp (‖v‖ ^ 2 / 4)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      ≤ ENNReal.ofReal (Real.exp (3 * d / 8)) := by
  rw [← map_pi_eq_stdGaussian, lintegral_map (by fun_prop) (by fun_prop)]
  have hprod : ∀ x : Fin d → ℝ,
      ENNReal.ofReal (Real.exp (‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2 / 4))
      = ∏ i, ENNReal.ofReal (Real.exp ((1 / 4) * x i ^ 2)) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
      EuclideanSpace.real_norm_sq_eq, Finset.sum_div]
    congr 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
    ring
  simp_rw [hprod]
  rw [l16_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp ((1 / 4) * x ^ 2)))
    (fun i => by fun_prop)]
  calc ∏ i : Fin d, ∫⁻ x, ENNReal.ofReal (Real.exp ((1 / 4) * x ^ 2)) ∂(gaussianReal 0 1)
      ≤ ∏ i : Fin d, ENNReal.ofReal (Real.exp (3 / 8)) :=
        Finset.prod_le_prod' (fun i _ => l16_sq1)
    _ = ENNReal.ofReal (Real.exp (3 * d / 8)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
        congr 2
        ring

theorem l16_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
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


open RobustGeneralization.GaussUpper in
theorem l16_prob {d : ℕ} (μ : E d) (σ : ℝ) : IsProbabilityMeasure (gaussVec μ σ) := by
  unfold gaussVec
  exact Measure.isProbabilityMeasure_map (by fun_prop)

open RobustGeneralization.GaussUpper in
theorem l16_mgf {d : ℕ} (μ : E d) (σ : ℝ) (h : E d) (t : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (t * inner ℝ x h)) ∂(gaussVec μ σ)
      = ENNReal.ofReal (Real.exp (t * inner ℝ μ h + t ^ 2 * σ ^ 2 * ‖h‖ ^ 2 / 2)) := by
  unfold gaussVec
  have hF : Measurable (fun x : E d => ENNReal.ofReal (Real.exp (t * inner ℝ x h))) :=
    (Real.measurable_exp.comp (measurable_const.mul
      (measurable_id.inner measurable_const))).ennreal_ofReal
  rw [lintegral_map hF (by fun_prop)]
  have e1 : ∀ v : E d, ENNReal.ofReal (Real.exp (t * inner ℝ (μ + σ • v) h))
      = ENNReal.ofReal (Real.exp (t * inner ℝ μ h)) *
        ENNReal.ofReal (Real.exp ((t * σ) * inner ℝ h v)) := by
    intro v
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    simp only [inner_add_left, real_inner_smul_left, real_inner_comm h v]
    ring
  simp_rw [e1]
  rw [lintegral_const_mul _ (by fun_prop), l16_mgfE,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

open RobustGeneralization.GaussUpper in
theorem l16_zbar_inner {d n : ℕ} (z : Fin n → E d) (h : E d) :
    inner ℝ (zbar' z) h = (n : ℝ)⁻¹ * ∑ i, inner ℝ (z i) h := by
  simp only [zbar', real_inner_smul_left, sum_inner]

open RobustGeneralization.GaussUpper in
theorem l16_zbar_meas {d n : ℕ} : Measurable (fun z : Fin n → E d => zbar' z) := by
  have h : Measurable (fun z : Fin n → E d => ∑ i, z i) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  exact h.const_smul ((n : ℝ)⁻¹)

open RobustGeneralization.GaussUpper in
theorem l16_tailA {d n : ℕ} (μ : E d) (hμ : ‖μ‖ = Real.sqrt d) (σ : ℝ) (hσ : 0 < σ)
    (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | inner ℝ (zbar' z) μ ≤ d - d / (2 * Real.sqrt n)}
      ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
  have := l16_prob μ σ
  set s : ℝ := Real.sqrt n with hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 < s := Real.sqrt_pos.2 hnpos
  have hs2 : s ^ 2 = n := Real.sq_sqrt hnpos.le
  set lam : ℝ := 1 / (2 * σ ^ 2 * s) with hlam
  have hl0 : 0 < lam := by positivity
  set g : (Fin n → E d) → ℝ := fun z => ∑ i, (-lam) * inner ℝ (z i) μ with hg
  have hfm : ∀ i : Fin n, Measurable (fun x : E d =>
      ENNReal.ofReal (Real.exp ((-lam) * inner ℝ x μ))) := fun i =>
    (Real.measurable_exp.comp (measurable_const.mul
      (measurable_id.inner measurable_const))).ennreal_ofReal
  have hgm : Measurable g := Finset.measurable_sum _ (fun i _ => measurable_const.mul
    ((measurable_pi_apply i).inner measurable_const))
  have hsub : {z : Fin n → E d | inner ℝ (zbar' z) μ ≤ d - d / (2 * s)}
      ⊆ {z | -(lam * (n * (d - d / (2 * s)))) ≤ g z} := by
    intro z hz
    simp only [Set.mem_ofPred_eq, l16_zbar_inner] at hz ⊢
    simp only [hg, ← Finset.mul_sum]
    have h1 : ∑ i, inner ℝ (z i) μ ≤ n * (d - d / (2 * s)) := by
      rw [inv_mul_le_iff₀ hnpos] at hz
      linarith
    nlinarith
  have hμμ : inner ℝ μ μ = (d : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hμ, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hprod : ∀ z : Fin n → E d, ENNReal.ofReal (Real.exp (g z))
      = ∏ i, ENNReal.ofReal (Real.exp ((-lam) * inner ℝ (z i) μ)) := by
    intro z
    rw [hg, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  calc (Measure.pi fun _ : Fin n => gaussVec μ σ) {z | inner ℝ (zbar' z) μ ≤ d - d / (2 * s)}
      ≤ (Measure.pi fun _ : Fin n => gaussVec μ σ)
          {z | -(lam * (n * (d - d / (2 * s)))) ≤ g z} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(-(lam * (n * (d - d / (2 * s))))))) *
          ∫⁻ z, ENNReal.ofReal (Real.exp (g z)) ∂(Measure.pi fun _ : Fin n => gaussVec μ σ) :=
        l16_markov _ g hgm _
    _ = ENNReal.ofReal (Real.exp (lam * (n * (d - d / (2 * s))))) *
          (ENNReal.ofReal (Real.exp ((-lam) * d + (-lam) ^ 2 * σ ^ 2 * d / 2))) ^ n := by
        simp_rw [hprod]
        rw [l16_pi_lint (gaussVec μ σ)
          (fun i x => ENNReal.ofReal (Real.exp ((-lam) * inner ℝ x μ))) hfm]
        simp_rw [l16_mgf]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, neg_neg, hμμ, hμ,
          Real.sq_sqrt (Nat.cast_nonneg _)]
    _ = ENNReal.ofReal (Real.exp (-((d : ℝ) / (8 * σ ^ 2)))) := by
        rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [hlam, ← hs2]
        field_simp
        ring
    _ ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        nlinarith

open RobustGeneralization.GaussUpper in
theorem l16_tailB {d n : ℕ} (μ : E d) (σ : ℝ) (hσ : 0 < σ) (hn : 1 ≤ n) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ) {z | 2 * σ ^ 2 * d / n ≤ ‖zbar' z - μ‖ ^ 2}
      ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
  have := l16_prob μ σ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set a : ℝ := Real.sqrt (n / (2 * σ ^ 2)) with ha
  have ha2 : a ^ 2 = n / (2 * σ ^ 2) := Real.sq_sqrt (by positivity)
  set g : (Fin n → E d) → ℝ := fun z => a ^ 2 * ‖zbar' z - μ‖ ^ 2 / 2 with hg
  have hgm : Measurable g :=
    (measurable_const.mul ((l16_zbar_meas.sub measurable_const).norm.pow_const 2)).div_const 2
  have hsub : {z : Fin n → E d | 2 * σ ^ 2 * d / n ≤ ‖zbar' z - μ‖ ^ 2}
      ⊆ {z | (d : ℝ) / 2 ≤ g z} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    simp only [hg]
    have h1 : a ^ 2 * (2 * σ ^ 2 * d / n) = d := by
      rw [ha2]
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hz (sq_nonneg a)
    linarith
  have hfm : ∀ v : E d, ∀ i : Fin n, Measurable (fun x : E d =>
      ENNReal.ofReal (Real.exp ((a / n) * inner ℝ x v))) := fun v i =>
    (Real.measurable_exp.comp (measurable_const.mul
      (measurable_id.inner measurable_const))).ennreal_ofReal
  have hkey : ∫⁻ z, ENNReal.ofReal (Real.exp (g z)) ∂(Measure.pi fun _ : Fin n => gaussVec μ σ)
      ≤ ENNReal.ofReal (Real.exp (3 * d / 8)) := by
    have hHS : ∀ z : Fin n → E d, ENNReal.ofReal (Real.exp (g z))
        = ∫⁻ v, ENNReal.ofReal (Real.exp (a * inner ℝ (zbar' z - μ) v)) ∂(stdGaussian (E d)) := by
      intro z
      rw [l16_mgfE]
    simp_rw [hHS]
    have hmeas : Measurable (Function.uncurry fun (z : Fin n → E d) (v : E d) =>
        ENNReal.ofReal (Real.exp (a * inner ℝ (zbar' z - μ) v))) :=
      (Real.measurable_exp.comp (measurable_const.mul
        (((l16_zbar_meas.comp measurable_fst).sub measurable_const).inner
          measurable_snd))).ennreal_ofReal
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have hin : ∀ v : E d, ∫⁻ z, ENNReal.ofReal (Real.exp (a * inner ℝ (zbar' z - μ) v))
        ∂(Measure.pi fun _ : Fin n => gaussVec μ σ) = ENNReal.ofReal (Real.exp (‖v‖ ^ 2 / 4)) := by
      intro v
      have hprod : ∀ z : Fin n → E d, ENNReal.ofReal (Real.exp (a * inner ℝ (zbar' z - μ) v))
          = ENNReal.ofReal (Real.exp (-(a * inner ℝ μ v))) *
            ∏ i, ENNReal.ofReal (Real.exp ((a / n) * inner ℝ (z i) v)) := by
        intro z
        rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [inner_sub_left, l16_zbar_inner, ← Finset.mul_sum]
        field_simp
        ring
      have hPm : Measurable (fun z : Fin n → E d =>
          ∏ i, ENNReal.ofReal (Real.exp ((a / n) * inner ℝ (z i) v))) :=
        Finset.measurable_prod _ (fun i _ => (hfm v i).comp (measurable_pi_apply i))
      simp_rw [hprod]
      rw [lintegral_const_mul _ hPm,
        l16_pi_lint (gaussVec μ σ)
          (fun i x => ENNReal.ofReal (Real.exp ((a / n) * inner ℝ x v))) (hfm v)]
      simp_rw [l16_mgf]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      have e1 : -(a * inner ℝ μ v) + (n : ℝ) * (a / n * inner ℝ μ v + (a / n) ^ 2 * σ ^ 2 * ‖v‖ ^ 2 / 2)
          = a ^ 2 * σ ^ 2 * ‖v‖ ^ 2 / (2 * n) := by
        field_simp
        ring
      rw [e1, ha2]
      field_simp
      ring
    simp_rw [hin]
    exact l16_sqE
  calc (Measure.pi fun _ : Fin n => gaussVec μ σ) {z | 2 * σ ^ 2 * d / n ≤ ‖zbar' z - μ‖ ^ 2}
      ≤ (Measure.pi fun _ : Fin n => gaussVec μ σ) {z | (d : ℝ) / 2 ≤ g z} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-((d : ℝ) / 2))) *
          ∫⁻ z, ENNReal.ofReal (Real.exp (g z)) ∂(Measure.pi fun _ : Fin n => gaussVec μ σ) :=
        l16_markov _ g hgm _
    _ ≤ ENNReal.ofReal (Real.exp (-((d : ℝ) / 2))) * ENNReal.ofReal (Real.exp (3 * d / 8)) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-((d : ℝ) / 8))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        rw [neg_div, neg_le_neg_iff]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg σ]

open RobustGeneralization.GaussUpper in
theorem l16_det (A N r s q σ : ℝ) (hσ : 0 < σ) (hs1 : 1 ≤ s) (hq : 0 < q)
    (hA : (2 * s - 1) * q ^ 2 < 2 * s * A) (hN : N ≤ q + r) (hN0 : 0 < N)
    (hrs : r * s < 2 * σ * q) :
    (2 * s - 1) / (2 * s + 4 * σ) * q < N⁻¹ * A := by
  have hs0 : 0 < s := by linarith
  have hc : 0 < (2 * s - 1) * q := by nlinarith
  have E1 : (2 * s - 1) * q * N ≤ (2 * s - 1) * q * (q + r) :=
    mul_le_mul_of_nonneg_left hN hc.le
  have E1s := mul_le_mul_of_nonneg_left E1 hs0.le
  have E2 := mul_lt_mul_of_pos_left hrs hc
  have E3 := mul_lt_mul_of_pos_left hA hσ
  have E4 := mul_lt_mul_of_pos_left hA hs0
  have key : s * ((2 * s - 1) * q * N) < s * (A * (2 * s + 4 * σ)) := by nlinarith
  have key' : (2 * s - 1) * q * N < A * (2 * s + 4 * σ) := lt_of_mul_lt_mul_left key hs0.le
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity), inv_mul_eq_div, div_mul_eq_mul_div,
    lt_div_iff₀ hN0]
  linarith

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem solution (d n : ℕ) (μ : E d) (hμ : ‖μ‖ = Real.sqrt d)
    (σ : ℝ) (hσ : 0 < σ) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | inner ℝ (what' z) μ ≤
          (2 * Real.sqrt n - 1) / (2 * Real.sqrt n + 4 * σ) * Real.sqrt d} ≤
      ENNReal.ofReal (2 * Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
  have := l16_prob μ σ
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine prob_le_one.trans ?_
    simp only [Nat.cast_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
    exact ENNReal.one_le_ofReal.2 (by norm_num)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hempty : {z : Fin 0 → E d | inner ℝ (what' z) μ ≤
          (2 * Real.sqrt (0 : ℕ) - 1) / (2 * Real.sqrt (0 : ℕ) + 4 * σ) * Real.sqrt d} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have hw : what' z = 0 := by simp [what', zbar']
      rw [hw, inner_zero_left]
      simp only [Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_sub, zero_add]
      have h1 : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
      have h2 : (-1 : ℝ) / (4 * σ) < 0 := div_neg_of_neg_of_pos (by norm_num) (by positivity)
      exact mul_neg_of_neg_of_pos h2 h1
    rw [hempty, measure_empty]
    exact bot_le
  have hn1 : 1 ≤ n := hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set s : ℝ := Real.sqrt n with hs
  set q : ℝ := Real.sqrt d with hq
  have hs0 : 0 < s := Real.sqrt_pos.2 hnpos
  have hs2 : s ^ 2 = n := Real.sq_sqrt hnpos.le
  have hs1 : 1 ≤ s := by
    rw [hs, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hq0 : 0 < q := Real.sqrt_pos.2 hdpos
  have hq2 : q ^ 2 = d := Real.sq_sqrt hdpos.le
  have hincl : {z : Fin n → E d | inner ℝ (what' z) μ ≤ (2 * s - 1) / (2 * s + 4 * σ) * q}
      ⊆ {z | inner ℝ (zbar' z) μ ≤ d - d / (2 * s)} ∪
        {z | 2 * σ ^ 2 * d / n ≤ ‖zbar' z - μ‖ ^ 2} := by
    intro z hz
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hc
    obtain ⟨hA, hB⟩ := hc
    simp only [Set.mem_ofPred_eq] at hz
    refine (not_lt.2 hz) ?_
    have hA2 : (2 * s - 1) * q ^ 2 < 2 * s * inner ℝ (zbar' z) μ := by
      have e : (d : ℝ) - d / (2 * s) = (2 * s - 1) * q ^ 2 / (2 * s) := by
        rw [hq2]; field_simp
      rw [e, div_lt_iff₀ (by positivity)] at hA
      linarith
    have hApos : 0 < inner ℝ (zbar' z) μ := by nlinarith
    have hz0 : zbar' z ≠ 0 := by
      intro h0
      rw [h0, inner_zero_left] at hApos
      exact lt_irrefl _ hApos
    have hN0 : 0 < ‖zbar' z‖ := norm_pos_iff.2 hz0
    have hN : ‖zbar' z‖ ≤ q + ‖zbar' z - μ‖ := by
      calc ‖zbar' z‖ = ‖μ + (zbar' z - μ)‖ := by congr 1; abel
        _ ≤ ‖μ‖ + ‖zbar' z - μ‖ := norm_add_le _ _
        _ = q + ‖zbar' z - μ‖ := by rw [hμ]
    have hrs : ‖zbar' z - μ‖ * s < 2 * σ * q := by
      have h1 : (‖zbar' z - μ‖ * s) ^ 2 < (2 * σ * q) ^ 2 := by
        rw [mul_pow, hs2]
        have h2 : ‖zbar' z - μ‖ ^ 2 * n < 2 * σ ^ 2 * d := by
          rw [lt_div_iff₀ hnpos] at hB; exact hB
        have h3 : (2 * σ * q) ^ 2 = 4 * σ ^ 2 * d := by rw [mul_pow, hq2]; ring
        rw [h3]
        nlinarith [sq_nonneg σ, mul_pos (pow_pos hσ 2) hdpos]
      exact (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h1
    have hw : inner ℝ (what' z) μ = ‖zbar' z‖⁻¹ * inner ℝ (zbar' z) μ := by
      simp only [what', real_inner_smul_left]
    rw [hw]
    exact l16_det _ _ _ s q σ hσ hs1 hq0 hA2 hN hN0 hrs
  calc (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | inner ℝ (what' z) μ ≤ (2 * s - 1) / (2 * s + 4 * σ) * q}
      ≤ (Measure.pi fun _ : Fin n => gaussVec μ σ)
          ({z | inner ℝ (zbar' z) μ ≤ d - d / (2 * s)} ∪
            {z | 2 * σ ^ 2 * d / n ≤ ‖zbar' z - μ‖ ^ 2}) := measure_mono hincl
    _ ≤ (Measure.pi fun _ : Fin n => gaussVec μ σ) {z | inner ℝ (zbar' z) μ ≤ d - d / (2 * s)}
        + (Measure.pi fun _ : Fin n => gaussVec μ σ)
            {z | 2 * σ ^ 2 * d / n ≤ ‖zbar' z - μ‖ ^ 2} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1))))
        + ENNReal.ofReal (Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) :=
        add_le_add (l16_tailA μ hμ σ hσ hn1) (l16_tailB μ σ hσ hn1)
    _ = ENNReal.ofReal (2 * Real.exp (-(d : ℝ) / (8 * (σ ^ 2 + 1)))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
