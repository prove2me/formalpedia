-- Prove2me | solution 1 for RobustGeneralization.GaussUpper.fact12_gaussian_norm_tail
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:43:10.428758+00:00
-- url     : https://prove2.me/submissions/e176490e-b041-448c-9697-e6728e5acad6

import Mathlib
import Definitions.Def_RobustGeneralization_GaussUpper_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem fx12_pi_lint {ι X : Type*} [Fintype ι] [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ S, ∏ i, f i (S i) ∂(Measure.pi fun _ : ι => ν) = ∏ i, ∫⁻ x, f i x ∂ν := by
  have hind : iIndepFun (fun i (S : ι → X) => f i (S i)) (Measure.pi fun _ : ι => ν) :=
    iIndepFun_pi (X := fun i => f i) (fun i => (hf i).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hf i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  exact (measurePreserving_eval (fun _ : ι => ν) i).lintegral_comp (hf i)

theorem fx12_gauss_sq_int (t : ℝ) (ht : t < 1 / 2) :
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

theorem fx12_sq1 (c : ℝ) (hc : c < 1 / 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x ^ 2)) ∂(gaussianReal 0 1)
      = ENNReal.ofReal ((Real.sqrt (1 - 2 * c))⁻¹) := by
  obtain ⟨hi, he⟩ := fx12_gauss_sq_int c hc
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)), he]

theorem fx12_sqE {d : ℕ} (c : ℝ) (hc : c < 1 / 2) :
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
  rw [fx12_pi_lint (gaussianReal 0 1) (fun i x => ENNReal.ofReal (Real.exp (c * x ^ 2)))
    (fun i => by fun_prop)]
  simp_rw [fx12_sq1 c hc]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (inv_nonneg.2 (Real.sqrt_nonneg _))]

theorem fx12_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℝ)
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

/-- Standard-Gaussian norm tail: for `s > 0`, `d ≥ 1`. -/
theorem fx12_std_tail {d : ℕ} (hd : 1 ≤ d) (s : ℝ) (hs : 0 < s) :
    stdGaussian (EuclideanSpace ℝ (Fin d)) {v | Real.sqrt d + s ≤ ‖v‖}
      ≤ ENNReal.ofReal (Real.exp (-s ^ 2 / 2)) := by
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
  have hsub : {v : EuclideanSpace ℝ (Fin d) | r + s ≤ ‖v‖} ⊆ {v | c * u ^ 2 ≤ c * ‖v‖ ^ 2} := by
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    apply mul_le_mul_of_nonneg_left _ hc0
    exact pow_le_pow_left₀ hu0.le hv 2
  refine (measure_mono hsub).trans ?_
  refine (fx12_markov _ (fun v => c * ‖v‖ ^ 2) (by fun_prop) (c * u ^ 2)).trans ?_
  rw [fx12_sqE c hch, hsq, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  -- exp(-c u²) (u/r)^d ≤ exp(-s²/2)
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

open RobustGeneralization.GaussUpper in
theorem solution (d : ℕ) (σ : ℝ) (hσ : 0 < σ) (t : ℝ) (ht : 0 ≤ t) :
    gaussVec (0 : E d) σ {z | σ * Real.sqrt d + t ≤ ‖z‖} ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * σ ^ 2))) := by
  have : IsProbabilityMeasure (gaussVec (0 : E d) σ) := by
    unfold gaussVec
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  rcases ht.eq_or_lt with h0 | htp
  · subst h0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
      Real.exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  have hmeas : MeasurableSet {z : E d | σ * Real.sqrt d + t ≤ ‖z‖} :=
    measurableSet_le measurable_const measurable_norm
  unfold gaussVec
  rw [Measure.map_apply (by fun_prop) hmeas]
  have hpre : (fun v : E d => (0 : E d) + σ • v) ⁻¹' {z | σ * Real.sqrt d + t ≤ ‖z‖}
      = {v : E d | Real.sqrt d + t / σ ≤ ‖v‖} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, zero_add, norm_smul, Real.norm_eq_abs,
      abs_of_pos hσ]
    constructor
    · intro h
      have : σ * (Real.sqrt d + t / σ) ≤ σ * ‖v‖ := by
        rw [mul_add, mul_div_cancel₀ _ hσ.ne']; exact h
      exact le_of_mul_le_mul_left this hσ
    · intro h
      have := mul_le_mul_of_nonneg_left h hσ.le
      rwa [mul_add, mul_div_cancel₀ _ hσ.ne'] at this
  rw [hpre]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have : {v : E 0 | Real.sqrt (0 : ℕ) + t / σ ≤ ‖v‖} = ∅ := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [Subsingleton.elim v 0, norm_zero]
      simp only [Nat.cast_zero, Real.sqrt_zero, zero_add]
      positivity
    rw [this, measure_empty]
    exact bot_le
  have key := fx12_std_tail hd (t / σ) (by positivity)
  refine key.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  congr 1
  field_simp
