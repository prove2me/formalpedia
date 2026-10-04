-- Prove2me | solution 1 for RobustGeneralization.GaussUpper.lemma13_sample_mean_norm_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:47:22.579503+00:00
-- url     : https://prove2.me/submissions/0ac75292-b303-4e14-9b4b-07909bf374f4

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem l13_mgf1 (s : ℝ) :
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

theorem l13_pi_lint {ι X : Type*} [Fintype ι] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ S, ∏ i, f i (S i) ∂(Measure.pi fun _ : ι => ν) = ∏ i, ∫⁻ x, f i x ∂ν := by
  have hind : iIndepFun (fun i (S : ι → X) => f i (S i)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi (X := fun i => f i) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : ι => ν) i).lintegral_comp (hf i)

theorem l13_mgfE {d : ℕ} (h : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
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
  rw [l13_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp ((t * h i) * x)))
    (fun i => by fun_prop)]
  simp_rw [l13_mgf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring


theorem l13_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
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
theorem l13_prob {d : ℕ} (m : E d) (s : ℝ) : IsProbabilityMeasure (gaussVec m s) := by
  unfold gaussVec
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem l13_gauss_sq_int (t : ℝ) (ht : t < 1 / 2) :
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

theorem l13_sq1 (c : ℝ) (hc : c < 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x ^ 2)) ∂(gaussianReal 0 1)
      = ENNReal.ofReal ((Real.sqrt (1 - 2 * c))⁻¹) := by
  obtain ⟨hi, he⟩ := l13_gauss_sq_int c hc
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)), he]

theorem l13_sqE {d : ℕ} (c : ℝ) (hc : c < 1 / 2) :
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
  rw [l13_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp (c * x ^ 2)))
    (fun i => by fun_prop)]
  simp_rw [l13_sq1 c hc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (inv_nonneg.2 (Real.sqrt_nonneg _))]

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem l13_gv_mgf {d : ℕ} (μ h : E d) (σ s : ℝ) :
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
  rw [lintegral_const_mul _ (by fun_prop), l13_mgfE, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem l13_zbar_meas {d n : ℕ} : Measurable (fun z : Fin n → E d => zbar' z) := by
  unfold zbar'
  fun_prop


open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem l13_hs {d n : ℕ} (hn : 0 < n) (μ : E d) (σ b : ℝ) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (b ^ 2 * ‖zbar' z - μ‖ ^ 2 / 2))
        ∂(Measure.pi fun _ : Fin n => gaussVec μ σ)
      = ∫⁻ v, ENNReal.ofReal (Real.exp ((b ^ 2 * σ ^ 2 / (2 * n)) * ‖v‖ ^ 2))
        ∂(stdGaussian (E d)) := by
  have hP : IsProbabilityMeasure (gaussVec μ σ) := l13_prob μ σ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set P := Measure.pi fun _ : Fin n => gaussVec μ σ with hPdef
  have hfm : ∀ v : E d, ∀ i : Fin n, Measurable (fun z : E d =>
      ENNReal.ofReal (Real.exp ((b / n) * inner ℝ z v))) := fun v i => by fun_prop
  have hHS : ∀ z : Fin n → E d, ENNReal.ofReal (Real.exp (b ^ 2 * ‖zbar' z - μ‖ ^ 2 / 2))
      = ∫⁻ v, ENNReal.ofReal (Real.exp (b * inner ℝ (zbar' z - μ) v)) ∂(stdGaussian (E d)) := by
    intro z
    rw [l13_mgfE]
  simp_rw [hHS]
  have hmeas : Measurable (Function.uncurry fun (z : Fin n → E d) (v : E d) =>
      ENNReal.ofReal (Real.exp (b * inner ℝ (zbar' z - μ) v))) :=
    (Real.measurable_exp.comp (measurable_const.mul
      (((l13_zbar_meas.comp measurable_fst).sub measurable_const).inner
        measurable_snd))).ennreal_ofReal
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hin : ∀ v : E d, ∫⁻ z, ENNReal.ofReal (Real.exp (b * inner ℝ (zbar' z - μ) v)) ∂P
      = ENNReal.ofReal (Real.exp ((b ^ 2 * σ ^ 2 / (2 * n)) * ‖v‖ ^ 2)) := by
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
      l13_pi_lint (gaussVec μ σ)
        (fun i z => ENNReal.ofReal (Real.exp ((b / n) * inner ℝ z v))) (hfm v)]
    simp_rw [l13_gv_mgf]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [hin]

theorem l13_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ)
    (hf : Measurable f) {d : ℕ} (hd : 1 ≤ d)
    (hmgf : ∀ c : ℝ, 0 ≤ c → c < 1 / 2 →
      ∫⁻ x, ENNReal.ofReal (Real.exp (c * f x ^ 2)) ∂P
        ≤ ENNReal.ofReal ((Real.sqrt (1 - 2 * c))⁻¹ ^ d))
    (s : ℝ) (hs : 0 < s) :
    P {x | Real.sqrt d + s ≤ f x} ≤ ENNReal.ofReal (Real.exp (-s ^ 2 / 2)) := by
  set r := Real.sqrt d with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hrr : r ^ 2 = d := Real.sq_sqrt (by positivity)
  set u := r + s with hu
  have hu0 : 0 < u := by linarith
  set c : ℝ := (1 - r ^ 2 / u ^ 2) / 2 with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    have : r ^ 2 / u ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have hch : c < 1 / 2 := by
    rw [hc]
    have : 0 < r ^ 2 / u ^ 2 := by positivity
    linarith
  have h12 : 1 - 2 * c = (r / u) ^ 2 := by rw [hc, div_pow]; ring
  have hsq : (Real.sqrt (1 - 2 * c))⁻¹ = u / r := by
    rw [h12, Real.sqrt_sq (by positivity), inv_div]
  have hsub : {x | r + s ≤ f x} ⊆ {x | c * u ^ 2 ≤ c * f x ^ 2} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    apply mul_le_mul_of_nonneg_left _ hc0
    exact pow_le_pow_left₀ hu0.le hx 2
  refine (measure_mono hsub).trans ?_
  refine (l13_markov _ (fun x => c * f x ^ 2) (by fun_prop) (c * u ^ 2)).trans ?_
  refine (mul_le_mul' le_rfl (hmgf c hc0 hch)).trans ?_
  rw [hsq, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have hur : u / r = 1 + s / r := by rw [hu]; field_simp
  have hpow : (u / r) ^ d ≤ Real.exp (s / r) ^ d := by
    rw [hur]
    apply pow_le_pow_left₀ (by positivity)
    have := Real.add_one_le_exp (s / r)
    linarith
  have hexp : Real.exp (s / r) ^ d = Real.exp (s * r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [← hrr]
    field_simp
  have hcu : c * u ^ 2 = (u ^ 2 - r ^ 2) / 2 := by
    rw [hc]; field_simp
  calc Real.exp (-(c * u ^ 2)) * (u / r) ^ d
      ≤ Real.exp (-(c * u ^ 2)) * Real.exp (s * r) := by
        rw [← hexp]; gcongr
    _ = Real.exp (-s ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        rw [hcu, hu]
        ring

open MeasureTheory ProbabilityTheory RobustGeneralization.GaussUpper in
theorem solution (d n : ℕ) (hn : 1 ≤ n) (μ : E d) (σ : ℝ) (hσ : 0 < σ)
    (δ : ℝ) (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => gaussVec μ σ)
        {z | ‖μ‖ + σ * (Real.sqrt d + Real.sqrt (2 * Real.log (1 / δ))) / Real.sqrt n ≤
          ‖zbar' z‖} ≤
      ENNReal.ofReal δ := by
  have hP : IsProbabilityMeasure (gaussVec μ σ) := l13_prob μ σ
  by_cases hδ1 : 1 ≤ δ
  · exact prob_le_one.trans (ENNReal.one_le_ofReal.2 hδ1)
  rw [not_le] at hδ1
  have hl : 0 < Real.log (1 / δ) := Real.log_pos (one_lt_one_div hδ hδ1)
  set s := Real.sqrt (2 * Real.log (1 / δ)) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = 2 * Real.log (1 / δ) := Real.sq_sqrt (by positivity)
  have hexpδ : Real.exp (-s ^ 2 / 2) = δ := by
    rw [hs2, show -(2 * Real.log (1 / δ)) / 2 = Real.log δ by
      rw [one_div, Real.log_inv]; ring, Real.exp_log hδ]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  set P := Measure.pi fun _ : Fin n => gaussVec μ σ with hPdef
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hempty : {z : Fin n → E 0 | ‖μ‖ + σ * (Real.sqrt (0 : ℕ) + s) / Real.sqrt n ≤
        ‖zbar' z‖} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [Subsingleton.elim (zbar' z) 0, Subsingleton.elim μ 0]
      simp only [norm_zero, zero_add, Nat.cast_zero, Real.sqrt_zero]
      positivity
    rw [hempty, measure_empty]
    exact bot_le
  set f : (Fin n → E d) → ℝ := fun z => Real.sqrt n * ‖zbar' z - μ‖ / σ with hfdef
  have hfm : Measurable f := by
    rw [hfdef]
    exact (measurable_const.mul (l13_zbar_meas.sub measurable_const).norm).div_const _
  have hsub : {z : Fin n → E d | ‖μ‖ + σ * (Real.sqrt d + s) / Real.sqrt n ≤ ‖zbar' z‖}
      ⊆ {z | Real.sqrt d + s ≤ f z} := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    have htri : ‖zbar' z‖ ≤ ‖μ‖ + ‖zbar' z - μ‖ := by
      have := norm_sub_norm_le (zbar' z) μ
      linarith
    have h1 : σ * (Real.sqrt d + s) / Real.sqrt n ≤ ‖zbar' z - μ‖ := by linarith
    rw [hfdef]
    simp only
    rw [le_div_iff₀ hσ]
    rw [div_le_iff₀ hsn] at h1
    linarith
  refine (measure_mono hsub).trans ?_
  have hmgf : ∀ c : ℝ, 0 ≤ c → c < 1 / 2 →
      ∫⁻ z, ENNReal.ofReal (Real.exp (c * f z ^ 2)) ∂P
        ≤ ENNReal.ofReal ((Real.sqrt (1 - 2 * c))⁻¹ ^ d) := by
    intro c hc0 hc
    set b := Real.sqrt (2 * c * n / σ ^ 2) with hb
    have hb2 : b ^ 2 = 2 * c * n / σ ^ 2 := Real.sq_sqrt (by positivity)
    have hpt : ∀ z, c * f z ^ 2 = b ^ 2 * ‖zbar' z - μ‖ ^ 2 / 2 := by
      intro z
      rw [hfdef, hb2]
      simp only
      rw [div_pow, mul_pow, Real.sq_sqrt hnR.le]
      field_simp
    simp_rw [hpt]
    rw [hPdef, l13_hs hn μ σ b]
    have hc' : b ^ 2 * σ ^ 2 / (2 * n) = c := by
      rw [hb2]; field_simp
    rw [hc', l13_sqE c hc]
  refine (l13_tail P f hfm hd hmgf s hs).trans (le_of_eq ?_)
  rw [hexpδ]
