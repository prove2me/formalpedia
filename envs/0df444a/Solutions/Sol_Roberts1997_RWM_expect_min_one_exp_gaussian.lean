-- Prove2me | solution 1 for Roberts1997.RWM.expect_min_one_exp_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T06:17:10.56027+00:00
-- url     : https://prove2.me/submissions/75e0cecb-5f5a-490d-b7cc-f2b7ad2cbb3e

import Definitions.Def_Roberts1997_RWM_Speed

/-!
# Proposition 2.4 of Roberts–Gelman–Gilks (1997): the Gaussian acceptance-rate formula

`𝔼[1 ∧ e^A] = Φ(μ/σ) + e^{μ+σ²/2} Φ(-σ - μ/σ)` for `A ~ N(μ, σ²)`, `σ > 0`.

* `min 1 (e^a)` equals `1` on `Ici 0` and `e^a` on `Iio 0`.
* The first piece is `P(A ≥ 0) = Φ(μ/σ)`: reduce `N(μ, σ²)` to the standard normal by the
  affine pushforward `z ↦ μ + σ z`, then use the symmetry `Φ(-t) = 1 - Φ(t)`.
* The second piece is the truncated lognormal mean: the exponential tilt
  `e^a φ_{μ,v}(a) = e^{μ+v/2} φ_{μ+v,v}(a)` (completion of the square) turns it into
  `e^{μ+σ²/2} P(N(μ+σ², σ²) ≤ 0) = e^{μ+σ²/2} Φ(-σ - μ/σ)`.
-/

open MeasureTheory ProbabilityTheory Roberts1997.RWM

open scoped NNReal

section Helpers

/-- The variance `(σ²).toNNReal` is nonzero when `σ > 0`. -/
private lemma sq_toNNReal_ne_zero {σ : ℝ} (hσ : 0 < σ) : (σ ^ 2 : ℝ).toNNReal ≠ 0 := by
  rw [ne_eq, Real.toNNReal_eq_zero, not_le]
  exact sq_pos_of_ne_zero hσ.ne'

/-- `gaussianReal μ σ²` is the pushforward of the standard normal under `z ↦ μ + σ z`. -/
private lemma gaussianReal_eq_map (μ : ℝ) {σ : ℝ} (_hσ : 0 < σ) :
    (gaussianReal 0 1).map (fun z => μ + σ * z) = gaussianReal μ (σ ^ 2).toNNReal := by
  have key : (gaussianReal 0 1).map (fun z => σ * z) = gaussianReal 0 ((σ ^ 2 : ℝ).toNNReal) := by
    rw [gaussianReal_map_const_mul (μ := 0) (v := 1) (c := σ),
      Real.toNNReal_of_nonneg (sq_nonneg σ)]
    simp
  rw [show (fun z => μ + σ * z) = (fun z => μ + z) ∘ (fun z => σ * z) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), key,
    gaussianReal_map_const_add (y := μ) (μ := 0), zero_add]

/-- The preimage of `Iic t` under `z ↦ μ + σ z` is `Iic ((t - μ)/σ)`. -/
private lemma preimage_Iic_affine (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (fun z => μ + σ * z) ⁻¹' Set.Iic t = Set.Iic ((t - μ) / σ) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic]
  constructor
  · intro h
    exact (le_div_iff₀ hσ).mpr (by linarith [mul_le_mul_of_nonneg_right h hσ.le])
  · intro h
    have h2 : z * σ ≤ t - μ := (le_div_iff₀ hσ).mp h
    linarith

/-- The `μ.real`-measure of `Iic 0` under `N(μ, σ²)` is `Φ(-μ/σ)`. -/
private lemma gaussianReal_real_Iic_zero (μ : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (gaussianReal μ (σ ^ 2).toNNReal).real (Set.Iic 0) = Phi (-(μ / σ)) := by
  rw [← gaussianReal_eq_map μ hσ, map_measureReal_apply (by fun_prop) measurableSet_Iic,
    preimage_Iic_affine μ hσ 0, zero_sub, neg_div, ← cdf_eq_real]
  rfl

/-- A Gaussian with nonzero variance has no atoms, so `Iio t` and `Iic t` carry equal mass. -/
private lemma gaussianReal_real_Iio_eq_Iic (μ' : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    (gaussianReal μ' v).real (Set.Iio t) = (gaussianReal μ' v).real (Set.Iic t) := by
  have h0 : (gaussianReal μ' v) ({t} : Set ℝ) = 0 :=
    (nullSingletonClass_gaussianReal hv).measure_singleton t
  have hreal0 : (gaussianReal μ' v).real ({t} : Set ℝ) = 0 := by
    simp [measureReal_def, h0]
  have hset : Set.Iio t ∪ ({t} : Set ℝ) = Set.Iic t := by
    ext z
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_Iio, Set.mem_Iic, le_iff_lt_or_eq]
  have hdisj : Disjoint (Set.Iio t) ({t} : Set ℝ) := by
    intro u hu1 hu2 x hx
    have h1 : x < t := hu1 hx
    have h2 : x = t := Set.mem_singleton_iff.mp (hu2 hx)
    rw [h2] at h1
    exact absurd h1 (lt_irrefl t)
  rw [← hset, measureReal_union hdisj (measurableSet_singleton t), hreal0, add_zero]

/-- Symmetry of the standard normal cdf: `Φ(-t) = 1 - Φ(t)`. -/
private lemma Phi_neg (t : ℝ) : Phi (-t) = 1 - Phi t := by
  have hneg : (gaussianReal 0 1).map Neg.neg = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := 0) (v := 1)
  have hpre : Neg.neg ⁻¹' Set.Ici t = Set.Iic (-t) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  have h1 : (gaussianReal 0 1).real (Set.Iic (-t)) = (gaussianReal 0 1).real (Set.Ici t) := by
    rw [← hpre, ← map_measureReal_apply (f := Neg.neg) (by fun_prop) measurableSet_Ici, hneg]
  have huniv : (gaussianReal 0 1).real Set.univ = 1 := by simp
  have h2 : (gaussianReal 0 1).real (Set.Ici t)
      + (gaussianReal 0 1).real (Set.Iio t) = 1 := by
    rw [← huniv, ← Set.compl_Ici]
    exact measureReal_add_measureReal_compl measurableSet_Ici
  have hio := gaussianReal_real_Iio_eq_Iic 0 one_ne_zero t
  have hPhi : Phi (-t) = (gaussianReal 0 1).real (Set.Iic (-t)) := by
    rw [← cdf_eq_real]; rfl
  have hPhi' : Phi t = (gaussianReal 0 1).real (Set.Iic t) := by
    rw [← cdf_eq_real]; rfl
  have h3 : (gaussianReal 0 1).real (Set.Ici t) = 1 - Phi t := by
    have h4 := h2
    rw [hio, ← hPhi'] at h4
    linarith
  rw [hPhi, h1, h3]

/-- The exponential tilt on Gaussian densities (completion of the square):
`φ_{μ,v}(a) (e^a c) = e^{μ+v/2} φ_{μ+v,v}(a) c`. -/
private lemma tilt_mul (μ' : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (a c : ℝ) :
    gaussianPDFReal μ' v a * (Real.exp a * c) =
      Real.exp (μ' + (v : ℝ) / 2) * (gaussianPDFReal (μ' + (v : ℝ)) v a * c) := by
  have hexp : Real.exp a * Real.exp (-(a - μ') ^ 2 / (2 * (v : ℝ))) =
      Real.exp (μ' + (v : ℝ) / 2)
        * Real.exp (-((a - (μ' + (v : ℝ))) ^ 2) / (2 * (v : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_eq_exp]
    field_simp
    ring
  simp only [gaussianPDFReal]
  linear_combination (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * c * hexp

/-- The truncated lognormal mean via the tilt:
`∫_{Iio 0} e^a dN(μ,v) = e^{μ+v/2} N(μ+v, v)(Iio 0)`. -/
private lemma tilt_integral (μ' : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ a, Real.exp a * Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a ∂(gaussianReal μ' v)
      = Real.exp (μ' + (v : ℝ) / 2) * (gaussianReal (μ' + (v : ℝ)) v).real (Set.Iio 0) := by
  have h1 : (∫ a, Real.exp a * Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a ∂(gaussianReal μ' v))
      = ∫ a, gaussianPDFReal μ' v a * (Real.exp a * Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a) := by
    rw [integral_gaussianReal_eq_integral_smul hv]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => smul_eq_mul _ _)
  have h3 : (∫ a, gaussianPDFReal μ' v a * (Real.exp a * Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a))
      = ∫ a, Real.exp (μ' + (v : ℝ) / 2)
          * (gaussianPDFReal (μ' + (v : ℝ)) v a * Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a) :=
    integral_congr_ae (Filter.Eventually.of_forall fun a => tilt_mul μ' hv a _)
  have h2 : (∫ a, gaussianPDFReal (μ' + (v : ℝ)) v a * Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a)
      = ∫ a, Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a ∂(gaussianReal (μ' + (v : ℝ)) v) := by
    have he : (∫ a, Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a ∂(gaussianReal (μ' + (v : ℝ)) v))
        = ∫ a, gaussianPDFReal (μ' + (v : ℝ)) v a • Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a :=
      integral_gaussianReal_eq_integral_smul hv
    rw [he]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => smul_eq_mul _ _)
  rw [h1, h3, integral_const_mul, h2, integral_indicator_one measurableSet_Iio]

/-- Integrability of a measurable function bounded by `1` on a finite measure. -/
private lemma integrable_of_abs_le_one {m : Measure ℝ} [IsFiniteMeasure m] {f : ℝ → ℝ}
    (hf : Measurable f) (h : ∀ a, |f a| ≤ 1) : Integrable f m := by
  refine (integrable_const (1 : ℝ)).mono hf.aestronglyMeasurable ?_
  filter_upwards with a
  simpa [Real.norm_eq_abs] using h a

end Helpers

theorem solution (μ σ : ℝ) (hσ : 0 < σ) :
    ∫ a, min 1 (Real.exp a) ∂(gaussianReal μ (σ ^ 2).toNNReal) =
      Phi (μ / σ) + Real.exp (μ + σ ^ 2 / 2) * Phi (-σ - μ / σ) := by
  have hv : (σ ^ 2 : ℝ).toNNReal ≠ 0 := sq_toNNReal_ne_zero hσ
  have hcoe : ((σ ^ 2 : ℝ).toNNReal : ℝ) = σ ^ 2 := Real.coe_toNNReal _ (sq_nonneg σ)
  -- pointwise split of the integrand
  have hsplit : ∀ a, min 1 (Real.exp a) =
      Set.indicator (Set.Ici 0) (1 : ℝ → ℝ) a
        + Real.exp a * Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a := by
    intro a
    by_cases ha : 0 ≤ a
    · have h1 : (1 : ℝ) ≤ Real.exp a := by
        rw [Real.one_le_exp_iff]
        exact ha
      rw [min_eq_left h1, Set.indicator_of_mem (Set.mem_Ici.mpr ha),
        Set.indicator_of_notMem (fun h => absurd (Set.mem_Iio.mp h) (not_lt.2 ha)),
        Pi.one_apply]
      ring
    · have ha' : a < 0 := not_le.mp ha
      have h1 : Real.exp a < 1 := by
        rw [Real.exp_lt_one_iff]
        exact ha'
      rw [min_eq_right (le_of_lt h1),
        Set.indicator_of_notMem (fun h => absurd (Set.mem_Ici.mp h) ha),
        Set.indicator_of_mem (Set.mem_Iio.mpr ha'), Pi.one_apply]
      ring
  -- integrability of the three integrands (all bounded by 1 in absolute value)
  have hint : Integrable (fun a => min 1 (Real.exp a)) (gaussianReal μ (σ ^ 2).toNNReal) := by
    refine integrable_of_abs_le_one (by fun_prop) ?_
    intro a
    exact abs_le.2 ⟨le_min (by norm_num) (by linarith [Real.exp_pos a]),
      min_le_left 1 (Real.exp a)⟩
  have hint1 : Integrable (fun a => Set.indicator (Set.Ici 0) (1 : ℝ → ℝ) a)
      (gaussianReal μ (σ ^ 2).toNNReal) := by
    refine integrable_of_abs_le_one ?_ ?_
    · exact measurable_const.indicator (measurableSet_Ici (a := 0))
    · intro a
      by_cases h : a ∈ Set.Ici 0
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
  have hint2 : Integrable (fun a => Real.exp a * Set.indicator (Set.Iio 0) (1 : ℝ → ℝ) a)
      (gaussianReal μ (σ ^ 2).toNNReal) := by
    refine integrable_of_abs_le_one ?_ ?_
    · exact Real.measurable_exp.mul
        (measurable_const.indicator (measurableSet_Iio (a := (0 : ℝ))))
    intro a
    by_cases ha : a ∈ Set.Iio 0
    · have ha' : a < 0 := Set.mem_Iio.mp ha
      rw [Set.indicator_of_mem ha, Pi.one_apply, mul_one,
        abs_of_nonneg (Real.exp_pos a).le]
      exact (Real.exp_lt_one_iff.mpr ha').le
    · rw [Set.indicator_of_notMem ha, mul_zero, abs_zero]
      norm_num
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_add hint1 hint2,
    integral_indicator_one measurableSet_Ici, tilt_integral μ hv]
  -- remaining goal: `m.real (Ici 0) + e^{μ+σ²/2} * m'.real (Iio 0) = RHS`
  have huniv : (gaussianReal μ (σ ^ 2).toNNReal).real Set.univ = 1 := by simp
  have hc : (gaussianReal μ (σ ^ 2).toNNReal).real (Set.Ici 0)
      + (gaussianReal μ (σ ^ 2).toNNReal).real (Set.Iio 0) = 1 := by
    rw [← huniv, ← Set.compl_Ici]
    exact measureReal_add_measureReal_compl measurableSet_Ici
  have hIio := gaussianReal_real_Iio_eq_Iic μ hv 0
  have hIic := gaussianReal_real_Iic_zero μ hσ
  have hPhi1 : (gaussianReal μ (σ ^ 2).toNNReal).real (Set.Ici 0) = Phi (μ / σ) := by
    have h4 := hc
    rw [hIio, hIic, Phi_neg (μ / σ)] at h4
    linarith
  have hfin : Real.exp (μ + ((σ ^ 2 : ℝ).toNNReal : ℝ) / 2)
      * (gaussianReal (μ + ((σ ^ 2 : ℝ).toNNReal : ℝ)) (σ ^ 2 : ℝ).toNNReal).real (Set.Iio 0)
      = Real.exp (μ + σ ^ 2 / 2) * Phi (-σ - μ / σ) := by
    rw [gaussianReal_real_Iio_eq_Iic _ hv 0, gaussianReal_real_Iic_zero _ hσ, hcoe]
    have hdiv : (μ + σ ^ 2) / σ = μ / σ + σ := by
      field_simp
    have harg : -(μ / σ + σ) = -σ - μ / σ := by
      field_simp
      ring
    rw [hdiv, harg]
  rw [hPhi1, hfin]
