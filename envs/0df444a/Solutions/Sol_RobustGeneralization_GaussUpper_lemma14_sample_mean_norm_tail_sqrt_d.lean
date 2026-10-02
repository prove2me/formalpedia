-- Prove2me | solution 1 for RobustGeneralization.GaussUpper.lemma14_sample_mean_norm_tail_sqrt_d
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T08:01:46.48341+00:00
-- url     : https://prove2.me/submissions/a8a5fba8-da47-49b7-91f3-02c0ebd9a635

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem l14_mgf1 (s : ℝ) :
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

theorem l14_pi_lint {ι X : Type*} [Fintype ι] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ S, ∏ i, f i (S i) ∂(Measure.pi fun _ : ι => ν) = ∏ i, ∫⁻ x, f i x ∂ν := by
  have hind : iIndepFun (fun i (S : ι → X) => f i (S i)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi (X := fun i => f i) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : ι => ν) i).lintegral_comp (hf i)

theorem l14_mgfE {d : ℕ} (h : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
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
  rw [l14_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp ((t * h i) * x)))
    (fun i => by fun_prop)]
  simp_rw [l14_mgf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring


theorem l14_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
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
theorem l14_prob {d : ℕ} (m : E d) (s : ℝ) : IsProbabilityMeasure (gaussVec m s) := by
  unfold gaussVec
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem l14_gauss_sq_int (t : ℝ) (ht : t < 1 / 2) :
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

theorem l14_sq1 (c : ℝ) (hc : c < 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x ^ 2)) ∂(gaussianReal 0 1)
      = ENNReal.ofReal ((Real.sqrt (1 - 2 * c))⁻¹) := by
  obtain ⟨hi, he⟩ := l14_gauss_sq_int c hc
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)), he]

theorem l14_sqE {d : ℕ} (c : ℝ) (hc : c < 1 / 2) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (c * ‖v‖ ^ 2)) ∂(stdGaussian (EuclideanSpace ℝ (Fin d)))
      = ENNReal.ofReal ((Real.sqrt (1 - 2 * c))⁻¹ ^ d) := by
  rw [← map_pi_eq_stdGaussian, lintegral_map (by fun_prop) (by fun_prop)]
  have hprod : ∀ x : Fin d → ℝ,
      ENNReal.ofReal (Real.exp (c * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ ^ 2))
      = ∏ i, ENNReal.ofReal (Real.exp (c * x i ^ 2)) := by
    intro x
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
      EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  simp_rw [hprod]
  rw [l14_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp (c * x ^ 2)))
    (fun i => by fun_prop)]
  simp_rw [l14_sq1 c hc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (inv_nonneg.2 (Real.sqrt_nonneg _))]

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem l14_gv_mgf {d : ℕ} (μ h : E d) (σ s : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (s * inner ℝ z h)) ∂(gaussVec μ σ)
      = ENNReal.ofReal (Real.exp (s * inner ℝ μ h + (s * σ) ^ 2 * ‖h‖ ^ 2 / 2)) := by
  unfold gaussVec
  rw [lintegral_map (by fun_prop) (by fun_prop)]
  have hh : ∀ v : E d, ENNReal.ofReal (Real.exp (s * inner ℝ (μ + σ • v) h))
      = ENNReal.ofReal (Real.exp (s * inner ℝ μ h)) *
          ENNReal.ofReal (Real.exp ((s * σ) * inner ℝ h v)) := by
    intro v
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    rw [inner_add_left, real_inner_smul_left, real_inner_comm h v]
    ring
  simp_rw [hh]
  rw [lintegral_const_mul _ (by fun_prop), l14_mgfE, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem l14_zbar_meas {d n : ℕ} : Measurable (fun z : Fin n → E d => zbar' z) := by
  unfold zbar'
  fun_prop

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem solution (d n : ℕ) (μ : E d) (hμ : ‖μ‖ = Real.sqrt d)
    (σ : ℝ) (hσ : 0 < σ) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | (1 + 2 * σ / Real.sqrt n) * Real.sqrt d ≤ ‖zbar' z‖} ≤
      ENNReal.ofReal (Real.exp (-(d : ℝ) / 2)) := by
  have hP : IsProbabilityMeasure (gaussVec μ σ) := l14_prob μ σ
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [CharP.cast_eq_zero, neg_zero, zero_div, Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hempty : {z : Fin 0 → E d | (1 + 2 * σ / Real.sqrt (0 : ℕ)) * Real.sqrt d ≤ ‖zbar' z‖}
        = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      simp only [zbar', Finset.univ_eq_empty, Finset.sum_empty, smul_zero, norm_zero,
        CharP.cast_eq_zero, Real.sqrt_zero, div_zero, add_zero, one_mul]
      exact Real.sqrt_pos.2 (by exact_mod_cast hd)
    rw [hempty, measure_empty]
    exact bot_le
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set P := Measure.pi fun _ : Fin n => gaussVec μ σ with hPdef
  set b : ℝ := Real.sqrt (3 * n / (4 * σ ^ 2)) with hb
  have hb2 : b ^ 2 = 3 * n / (4 * σ ^ 2) := Real.sq_sqrt (by positivity)
  set g : (Fin n → E d) → ℝ := fun z => b ^ 2 * ‖zbar' z - μ‖ ^ 2 / 2 with hg
  have hgm : Measurable g := by
    rw [hg]
    exact (measurable_const.mul ((l14_zbar_meas.sub measurable_const).norm.pow_const 2)).div_const 2
  have hsub : {z : Fin n → E d | (1 + 2 * σ / Real.sqrt n) * Real.sqrt d ≤ ‖zbar' z‖}
      ⊆ {z | 3 * (d : ℝ) / 2 ≤ g z} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    simp only [hg]
    have htri : ‖zbar' z‖ - ‖μ‖ ≤ ‖zbar' z - μ‖ := norm_sub_norm_le _ _
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
    have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    have h1 : 2 * σ / Real.sqrt n * Real.sqrt d ≤ ‖zbar' z - μ‖ := by
      rw [hμ] at htri
      nlinarith
    have h0 : 0 ≤ 2 * σ / Real.sqrt n * Real.sqrt d := by positivity
    have h2 : (2 * σ / Real.sqrt n * Real.sqrt d) ^ 2 ≤ ‖zbar' z - μ‖ ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have h3 : (2 * σ / Real.sqrt n * Real.sqrt d) ^ 2 = 4 * σ ^ 2 * d / n := by
      rw [div_mul_eq_mul_div, div_pow, mul_pow, mul_pow, Real.sq_sqrt hnR.le,
        Real.sq_sqrt hdR.le]
      ring
    rw [h3] at h2
    have h4 : b ^ 2 * (4 * σ ^ 2 * d / n) / 2 = 3 * d / 2 := by
      rw [hb2]
      field_simp
    have h5 := mul_le_mul_of_nonneg_left h2 (sq_nonneg b)
    linarith
  have hfm : ∀ v : E d, ∀ i : Fin n, Measurable (fun z : E d =>
      ENNReal.ofReal (Real.exp ((b / n) * inner ℝ z v))) := fun v i => by fun_prop
  have hkey : ∫⁻ z, ENNReal.ofReal (Real.exp (g z)) ∂P ≤ ENNReal.ofReal (2 ^ d) := by
    have hHS : ∀ z : Fin n → E d, ENNReal.ofReal (Real.exp (g z))
        = ∫⁻ v, ENNReal.ofReal (Real.exp (b * inner ℝ (zbar' z - μ) v)) ∂(stdGaussian (E d)) := by
      intro z
      rw [l14_mgfE]
    simp_rw [hHS]
    have hmeas : Measurable (Function.uncurry fun (z : Fin n → E d) (v : E d) =>
        ENNReal.ofReal (Real.exp (b * inner ℝ (zbar' z - μ) v))) :=
      (Real.measurable_exp.comp (measurable_const.mul
        (((l14_zbar_meas.comp measurable_fst).sub measurable_const).inner
          measurable_snd))).ennreal_ofReal
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have hin : ∀ v : E d, ∫⁻ z, ENNReal.ofReal (Real.exp (b * inner ℝ (zbar' z - μ) v)) ∂P
        = ENNReal.ofReal (Real.exp ((3 / 8) * ‖v‖ ^ 2)) := by
      intro v
      have hprod : ∀ z : Fin n → E d, ENNReal.ofReal (Real.exp (b * inner ℝ (zbar' z - μ) v))
          = ENNReal.ofReal (Real.exp (-(b * inner ℝ μ v))) *
            ∏ i, ENNReal.ofReal (Real.exp ((b / n) * inner ℝ (z i) v)) := by
        intro z
        rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [inner_sub_left]
        simp only [zbar', real_inner_smul_left, sum_inner]
        rw [← Finset.mul_sum]
        field_simp
        ring
      have hPm : Measurable (fun z : Fin n → E d =>
          ∏ i, ENNReal.ofReal (Real.exp ((b / n) * inner ℝ (z i) v))) :=
        Finset.measurable_prod _ (fun i _ => (hfm v i).comp (measurable_pi_apply i))
      simp_rw [hprod]
      rw [hPdef, lintegral_const_mul _ hPm,
        l14_pi_lint (gaussVec μ σ)
          (fun i z => ENNReal.ofReal (Real.exp ((b / n) * inner ℝ z v))) (hfm v)]
      simp_rw [l14_gv_mgf]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      have e1 : -(b * inner ℝ μ v) + (n : ℝ) * (b / n * inner ℝ μ v + (b / n * σ) ^ 2 * ‖v‖ ^ 2 / 2)
          = b ^ 2 * σ ^ 2 * ‖v‖ ^ 2 / (2 * n) := by
        field_simp
        ring
      rw [e1, hb2]
      field_simp
      ring
    simp_rw [hin]
    rw [l14_sqE (3 / 8) (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    have hs : Real.sqrt (1 - 2 * (3 / 8 : ℝ)) = 1 / 2 := by
      rw [show (1 : ℝ) - 2 * (3 / 8) = (1 / 2) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [hs]
    norm_num
  calc P {z | (1 + 2 * σ / Real.sqrt n) * Real.sqrt d ≤ ‖zbar' z‖}
      ≤ P {z | 3 * (d : ℝ) / 2 ≤ g z} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(3 * (d : ℝ) / 2))) * ∫⁻ z, ENNReal.ofReal (Real.exp (g z)) ∂P :=
        l14_markov _ g hgm _
    _ ≤ ENNReal.ofReal (Real.exp (-(3 * (d : ℝ) / 2))) * ENNReal.ofReal (2 ^ d) := by
        gcongr
    _ ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / 2)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        have he : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
        have h2 : (2 : ℝ) ^ d ≤ Real.exp d := by
          calc (2 : ℝ) ^ d ≤ Real.exp 1 ^ d := pow_le_pow_left₀ (by norm_num) he d
            _ = Real.exp d := by rw [← Real.exp_nat_mul, mul_one]
        calc Real.exp (-(3 * (d : ℝ) / 2)) * 2 ^ d
            ≤ Real.exp (-(3 * (d : ℝ) / 2)) * Real.exp d := by gcongr
          _ = Real.exp (-(d : ℝ) / 2) := by
            rw [← Real.exp_add]
            congr 1
            ring
