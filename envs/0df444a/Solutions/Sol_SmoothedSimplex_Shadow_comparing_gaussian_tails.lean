-- Prove2me | solution 1 for SmoothedSimplex.Shadow.comparing_gaussian_tails
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-10-28T07:22:56.330977+00:00
-- url     : https://prove2.me/submissions/9da13463-c5a6-4f30-a72f-b4766a2b348b

import Mathlib

namespace Prove2SwarmSubmission

namespace SmoothedSimplex.Shadow.NativeTailEndpoints

open MeasureTheory ProbabilityTheory

theorem epsilon_nonneg (x y ε : ℝ) (hxy : |x - y| ≤ ε) : 0 ≤ ε :=
  le_trans (abs_nonneg (x - y)) hxy

theorem shift_le_epsilon (x y ε : ℝ) (hxy : |x - y| ≤ ε) : y - x ≤ ε := by
  have h := (abs_le.mp hxy).1
  linarith

theorem tail_antitone (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Antitone (fun x : ℝ => (μ (Set.Ici x)).toReal) := by
  intro x y hxy
  exact ENNReal.toReal_mono (measure_ne_top μ (Set.Ici x))
    (measure_mono (fun _ hz => le_trans hxy hz))

theorem scaled_tail_le_of_y_le_x (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x y c : ℝ) (hyx : y ≤ x) (hc : c ≤ 1) :
    c * (μ (Set.Ici x)).toReal ≤ (μ (Set.Ici y)).toReal := by
  calc
    c * (μ (Set.Ici x)).toReal ≤ 1 * (μ (Set.Ici x)).toReal :=
      mul_le_mul_of_nonneg_right hc ENNReal.toReal_nonneg
    _ ≤ (μ (Set.Ici y)).toReal := by
      simpa only [one_mul] using tail_antitone μ hyx

theorem scaled_tail_le_of_nonpos (μ : Measure ℝ)
    (x y c : ℝ) (hc : c ≤ 0) :
    c * (μ (Set.Ici x)).toReal ≤ (μ (Set.Ici y)).toReal :=
  le_trans (mul_nonpos_of_nonpos_of_nonneg hc ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg

theorem coefficient_le_one (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 ≤ ε) :
    1 - 8 * ε / (3 * σ ^ 2) ≤ 1 := by
  have hden : 0 < 3 * σ ^ 2 := by positivity
  have hratio : 0 ≤ 8 * ε / (3 * σ ^ 2) :=
    div_nonneg (mul_nonneg (by norm_num) hε) hden.le
  linarith

theorem coefficient_nonpos_of_large_epsilon (σ ε : ℝ) (hσ : 0 < σ)
    (hε : 3 * σ ^ 2 / 8 ≤ ε) :
    1 - 8 * ε / (3 * σ ^ 2) ≤ 0 := by
  have hden : 0 < 3 * σ ^ 2 := by positivity
  have hnum : 1 * (3 * σ ^ 2) ≤ 8 * ε := by linarith
  have hratio : 1 ≤ 8 * ε / (3 * σ ^ 2) := (le_div_iff₀ hden).2 hnum
  linarith

theorem comparison_of_y_le_x (σ : ℝ) (hσ : 0 < σ) (x y ε : ℝ)
    (hxy : |x - y| ≤ ε) (hyx : y ≤ x) :
    (1 - 8 * ε / (3 * σ ^ 2)) *
        (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by
  exact scaled_tail_le_of_y_le_x (gaussianReal 0 (σ ^ 2).toNNReal) x y
    (1 - 8 * ε / (3 * σ ^ 2)) hyx
    (coefficient_le_one σ ε hσ (epsilon_nonneg x y ε hxy))

theorem comparison_of_large_epsilon (σ : ℝ) (hσ : 0 < σ) (x y ε : ℝ)
    (hε : 3 * σ ^ 2 / 8 ≤ ε) :
    (1 - 8 * ε / (3 * σ ^ 2)) *
        (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by
  exact scaled_tail_le_of_nonpos (gaussianReal 0 (σ ^ 2).toNNReal) x y
    (1 - 8 * ε / (3 * σ ^ 2)) (coefficient_nonpos_of_large_epsilon σ ε hσ hε)

theorem comparison_of_nonpositive_multiplier (σ x y ε : ℝ)
    (hc : 1 - 8 * ε / (3 * σ ^ 2) ≤ 0) :
    (1 - 8 * ε / (3 * σ ^ 2)) *
        (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by
  exact scaled_tail_le_of_nonpos (gaussianReal 0 (σ ^ 2).toNNReal) x y
    (1 - 8 * ε / (3 * σ ^ 2)) hc

theorem comparison_same_threshold (σ : ℝ) (hσ : 0 < σ) (x ε : ℝ)
    (hε : 0 ≤ ε) :
    (1 - 8 * ε / (3 * σ ^ 2)) *
        (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal := by
  exact scaled_tail_le_of_y_le_x (gaussianReal 0 (σ ^ 2).toNNReal) x x
    (1 - 8 * ε / (3 * σ ^ 2)) le_rfl (coefficient_le_one σ ε hσ hε)

theorem comparison_epsilon_zero (σ x y : ℝ) (hxy : |x - y| ≤ 0) :
    (1 - 8 * (0 : ℝ) / (3 * σ ^ 2)) *
        (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by
  have heq : x = y := sub_eq_zero.mp
    (abs_eq_zero.mp (le_antisymm hxy (abs_nonneg (x - y))))
  subst y
  simp

theorem comparison_reduce_to_small_positive_shift (σ : ℝ) (hσ : 0 < σ)
    (x y ε : ℝ) (hxy : |x - y| ≤ ε)
    (hsmall : x < y → ε < 3 * σ ^ 2 / 8 →
      (1 - 8 * ε / (3 * σ ^ 2)) *
          (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
        (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal) :
    (1 - 8 * ε / (3 * σ ^ 2)) *
        (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by
  by_cases hyx : y ≤ x
  · exact comparison_of_y_le_x σ hσ x y ε hxy hyx
  by_cases hlarge : 3 * σ ^ 2 / 8 ≤ ε
  · exact comparison_of_large_epsilon σ hσ x y ε hlarge
  exact hsmall (lt_of_not_ge hyx) (lt_of_not_ge hlarge)

end SmoothedSimplex.Shadow.NativeTailEndpoints

namespace NativeGaussianTailIntegral

open MeasureTheory Set

/-- The mass lost by raising a cutoff is exactly the integral between the cutoffs. -/
theorem tail_integral_sub_eq_intervalIntegral {f : ℝ → ℝ} (hf : Integrable f)
    {x y : ℝ} (hxy : x ≤ y) :
    (∫ t in Ici x, f t) - (∫ t in Ici y, f t) = ∫ t in x..y, f t := by
  have hset : Ici x \ Ici y = Ico x y := by
    ext t
    simp only [mem_sdiff, mem_Ici, mem_Ico, not_le]
  have hsubset : Ici y ⊆ Ici x := fun _ ht => hxy.trans ht
  have hdiff : (∫ t in Ico x y, f t) =
      (∫ t in Ici x, f t) - (∫ t in Ici y, f t) := by
    simpa only [hset] using
      (setIntegral_sdiff measurableSet_Ici
        (hf.integrableOn : IntegrableOn f (Ici x)) hsubset)
  calc
    (∫ t in Ici x, f t) - (∫ t in Ici y, f t) = ∫ t in Ico x y, f t := hdiff.symm
    _ = ∫ t in Icc x y, f t := integral_Icc_eq_integral_Ico.symm
    _ = ∫ t in Ioc x y, f t := integral_Icc_eq_integral_Ioc
    _ = ∫ t in x..y, f t := (intervalIntegral.integral_of_le hxy).symm

/-- A pointwise density ceiling controls the loss of upper-tail integral. -/
theorem tail_integral_loss_le {f : ℝ → ℝ} (hf : Integrable f)
    {x y M : ℝ} (hxy : x ≤ y) (hM : ∀ t ∈ Icc x y, f t ≤ M) :
    (∫ t in Ici x, f t) - (∫ t in Ici y, f t) ≤ (y - x) * M := by
  rw [tail_integral_sub_eq_intervalIntegral hf hxy]
  calc
    (∫ t in x..y, f t) ≤ ∫ _t in x..y, M :=
      intervalIntegral.integral_mono_on hxy hf.intervalIntegrable intervalIntegrable_const hM
    _ = (y - x) * M := by
      rw [intervalIntegral.integral_const, smul_eq_mul]

/-- Replacing the cutoff displacement by its upper bound preserves the loss estimate. -/
theorem tail_integral_loss_le_epsilon {f : ℝ → ℝ} (hf : Integrable f)
    {x y ε M : ℝ} (hxy : x ≤ y) (hε : y - x ≤ ε) (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Icc x y, f t ≤ M) :
    (∫ t in Ici x, f t) - (∫ t in Ici y, f t) ≤ ε * M :=
  (tail_integral_loss_le hf hxy hM).trans (mul_le_mul_of_nonneg_right hε hM0)

/-- A relative density ceiling yields the multiplicative upper-tail comparison. -/
theorem tail_integral_comparison_of_density_bound {f : ℝ → ℝ} (hf : Integrable f)
    {x y ε C : ℝ} (hxy : x ≤ y) (hε : y - x ≤ ε) (hC : 0 ≤ C)
    (hTail : 0 ≤ ∫ t in Ici x, f t)
    (hbound : ∀ t ∈ Icc x y, f t ≤ C * (∫ u in Ici x, f u)) :
    (1 - C * ε) * (∫ t in Ici x, f t) ≤ ∫ t in Ici y, f t := by
  have hloss := tail_integral_loss_le hf hxy hbound
  have hwidth := mul_le_mul_of_nonneg_right hε (mul_nonneg hC hTail)
  nlinarith only [hloss, hwidth]

/-- Nonnegativity of the density supplies the tail-sign premise. -/
theorem tail_integral_comparison_of_nonneg_density {f : ℝ → ℝ} (hf : Integrable f)
    (hf0 : ∀ t, 0 ≤ f t) {x y ε C : ℝ} (hxy : x ≤ y) (hε : y - x ≤ ε)
    (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc x y, f t ≤ C * (∫ u in Ici x, f u)) :
    (1 - C * ε) * (∫ t in Ici x, f t) ≤ ∫ t in Ici y, f t :=
  tail_integral_comparison_of_density_bound hf hxy hε hC (integral_nonneg hf0) hbound

/-- The finite-measure counterpart needs no density representation or atomlessness. -/
theorem tail_measure_sub_eq_Ico (μ : Measure ℝ) [IsFiniteMeasure μ]
    {x y : ℝ} (hxy : x ≤ y) :
    (μ (Ici x)).toReal - (μ (Ici y)).toReal = (μ (Ico x y)).toReal := by
  have hset : Ici x \ Ici y = Ico x y := by
    ext t
    simp only [mem_sdiff, mem_Ici, mem_Ico, not_le]
  have hsubset : Ici y ⊆ Ici x := fun _ ht => hxy.trans ht
  have hdiff : μ.real (Ici x \ Ici y) = μ.real (Ici x) - μ.real (Ici y) :=
    measureReal_sdiff hsubset measurableSet_Ici
  rw [hset] at hdiff
  exact hdiff.symm

/-- An interval-mass ceiling directly yields comparison of finite-measure tails. -/
theorem tail_measure_comparison_of_interval_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {x y ε C : ℝ} (hxy : x ≤ y) (hε : y - x ≤ ε) (hC : 0 ≤ C)
    (hsegment : (μ (Ico x y)).toReal ≤
      (y - x) * (C * (μ (Ici x)).toReal)) :
    (1 - C * ε) * (μ (Ici x)).toReal ≤ (μ (Ici y)).toReal := by
  have hloss := (tail_measure_sub_eq_Ico μ hxy).trans_le hsegment
  have hwidth := mul_le_mul_of_nonneg_right hε
    (mul_nonneg hC (ENNReal.toReal_nonneg : 0 ≤ (μ (Ici x)).toReal))
  nlinarith only [hloss, hwidth]

end NativeGaussianTailIntegral

namespace SmoothedSimplex.Shadow.NativeTailDensity

open MeasureTheory ProbabilityTheory
open scoped NNReal

theorem gaussian_mass_eq_integral (v : ℝ≥0) (hv : v ≠ 0) (s : Set ℝ) :
    (gaussianReal 0 v s).toReal = ∫ z in s, gaussianPDFReal 0 v z := by
  rw [gaussianReal_apply_eq_integral 0 hv s]
  exact ENNReal.toReal_ofReal
    (integral_nonneg (fun z => gaussianPDFReal_nonneg 0 v z))

theorem density_le_at_zero (v : ℝ≥0) (z : ℝ) :
    gaussianPDFReal 0 v z ≤ gaussianPDFReal 0 v 0 := by
  simp only [gaussianPDFReal, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg z]) (by positivity)

theorem density_le_of_nonneg_le (v : ℝ≥0) (x z : ℝ)
    (hx : 0 ≤ x) (hxz : x ≤ z) :
    gaussianPDFReal 0 v z ≤ gaussianPDFReal 0 v x := by
  simp only [gaussianPDFReal, sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq : x ^ 2 ≤ z ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)

theorem local_density_bound_of_sign (v : ℝ≥0) (T : ℝ → ℝ) (C x : ℝ)
    (hC : 0 ≤ C) (hT : Antitone T)
    (hzero : gaussianPDFReal 0 v 0 ≤ C * T 0)
    (hpositive : 0 < x → gaussianPDFReal 0 v x ≤ C * T x) :
    ∀ z : ℝ, x ≤ z → gaussianPDFReal 0 v z ≤ C * T x := by
  intro z hxz
  by_cases hx : x ≤ 0
  · exact (density_le_at_zero v z).trans
      (hzero.trans (mul_le_mul_of_nonneg_left (hT hx) hC))
  · exact (density_le_of_nonneg_le v x z (le_of_lt (lt_of_not_ge hx)) hxz).trans
      (hpositive (lt_of_not_ge hx))

theorem comparison_of_loss_bound (σ x y ε M A B : ℝ)
    (hε : y - x ≤ ε) (hM : 0 ≤ M)
    (hrel : M ≤ (8 / (3 * σ ^ 2)) * A)
    (hε0 : 0 ≤ ε) (hloss : A - B ≤ (y - x) * M) :
    (1 - 8 * ε / (3 * σ ^ 2)) * A ≤ B := by
  have hbound : A - B ≤ ε * ((8 / (3 * σ ^ 2)) * A) :=
    hloss.trans ((mul_le_mul_of_nonneg_right hε hM).trans
      (mul_le_mul_of_nonneg_left hrel hε0))
  have hid : (1 - 8 * ε / (3 * σ ^ 2)) * A =
      A - ε * ((8 / (3 * σ ^ 2)) * A) := by ring
  rw [hid]
  linarith

end SmoothedSimplex.Shadow.NativeTailDensity

namespace SmoothedSimplex.Shadow.NativeTailAssembly

open MeasureTheory ProbabilityTheory

theorem comparison_of_local_hazard (σ : ℝ) (hσ : 0 < σ) (x y ε : ℝ)
    (hxy : |x - y| ≤ ε)
    (hbound : ∀ z ∈ Set.Icc x y,
      gaussianPDFReal 0 (σ ^ 2).toNNReal z ≤
        (8 / (3 * σ ^ 2)) * (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal) :
    (1 - 8 * ε / (3 * σ ^ 2)) *
        (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by
  by_cases hyx : y ≤ x
  · exact NativeTailEndpoints.comparison_of_y_le_x σ hσ x y ε hxy hyx
  have hle : x ≤ y := le_of_lt (lt_of_not_ge hyx)
  have hv : (σ ^ 2).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos hσ))
  have hC : 0 ≤ 8 / (3 * σ ^ 2) := by positivity
  have hbound' : ∀ z ∈ Set.Icc x y,
      gaussianPDFReal 0 (σ ^ 2).toNNReal z ≤
        (8 / (3 * σ ^ 2)) *
          (∫ u in Set.Ici x, gaussianPDFReal 0 (σ ^ 2).toNNReal u) := by
    intro z hz
    rw [← NativeTailDensity.gaussian_mass_eq_integral (σ ^ 2).toNNReal hv (Set.Ici x)]
    exact hbound z hz
  have h := NativeGaussianTailIntegral.tail_integral_comparison_of_nonneg_density
    (integrable_gaussianPDFReal 0 (σ ^ 2).toNNReal)
    (gaussianPDFReal_nonneg 0 (σ ^ 2).toNNReal) hle
    (NativeTailEndpoints.shift_le_epsilon x y ε hxy) hC hbound'
  rw [← NativeTailDensity.gaussian_mass_eq_integral (σ ^ 2).toNNReal hv (Set.Ici x),
    ← NativeTailDensity.gaussian_mass_eq_integral (σ ^ 2).toNNReal hv (Set.Ici y)] at h
  have hcoef : 1 - (8 / (3 * σ ^ 2)) * ε = 1 - 8 * ε / (3 * σ ^ 2) := by ring
  rw [hcoef] at h
  exact h

theorem comparison_of_zero_and_positive_hazards (σ : ℝ) (hσ : 0 < σ)
    (x y ε : ℝ) (hxy : |x - y| ≤ ε)
    (hzero : gaussianPDFReal 0 (σ ^ 2).toNNReal 0 ≤
      (8 / (3 * σ ^ 2)) * (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici 0)).toReal)
    (hpositive : 0 < x → gaussianPDFReal 0 (σ ^ 2).toNNReal x ≤
      (8 / (3 * σ ^ 2)) * (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal) :
    (1 - 8 * ε / (3 * σ ^ 2)) *
        (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by
  apply comparison_of_local_hazard σ hσ x y ε hxy
  intro z hz
  exact NativeTailDensity.local_density_bound_of_sign (σ ^ 2).toNNReal
    (fun a => (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici a)).toReal)
    (8 / (3 * σ ^ 2)) x (by positivity)
    (NativeTailEndpoints.tail_antitone (gaussianReal 0 (σ ^ 2).toNNReal))
    hzero hpositive z hz.1

end SmoothedSimplex.Shadow.NativeTailAssembly

/-! Hazard bound for `SmoothedSimplex.Shadow.comparing_gaussian_tails` (graph-scout seat %72).

Owner interface: analysis-prover's INTERFACE.md v2 (sha256 22b17b10). This is a helper only and
does not prove the frozen target. For `0 < σ ≤ 1` and every `x ≤ 2`, the Gaussian density at `x`
is at most `8 / (3σ²)` times the tail integral over `Set.Ici x`.

Route: for `s ≥ x` and `x ≤ 2`, `φ(s) ≥ φ(x)·exp(-(2/σ²)(s - x))·(1 - (s - x)²/(2σ²))`.
Integrating that lower bound over `[x, x + 2]` with an explicit antiderivative gives at least
`φ(x)(σ²/2 - σ⁴/8) ≥ (3σ²/8)·φ(x)`. -/

namespace SmoothedSimplex.Shadow.GraphScoutHazard

open MeasureTheory ProbabilityTheory

/-- Explicit centred Gaussian density with variance `σ²`. -/
private theorem gs_pdf_eq (σ s : ℝ) :
    gaussianPDFReal 0 (σ ^ 2).toNNReal s =
      (Real.sqrt (2 * Real.pi * σ ^ 2))⁻¹ * Real.exp (-s ^ 2 / (2 * σ ^ 2)) := by
  rw [gaussianPDFReal, Real.coe_toNNReal _ (sq_nonneg σ), sub_zero]

/-- Pointwise exponent comparison: for `x ≤ 2` and `x ≤ s`,
`e^{-x²/2σ²} · e^{-(2/σ²)(s-x)} · (1 - (s-x)²/2σ²) ≤ e^{-s²/2σ²}`. -/
private theorem gs_exp_shift_lower (σ : ℝ) (hσ : 0 < σ) (x s : ℝ) (hx : x ≤ 2) (hxs : x ≤ s) :
    Real.exp (-x ^ 2 / (2 * σ ^ 2)) *
        (Real.exp (-(2 / σ ^ 2) * (s - x)) * (1 - (s - x) ^ 2 / (2 * σ ^ 2))) ≤
      Real.exp (-s ^ 2 / (2 * σ ^ 2)) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hσ2 : 0 < 2 * σ ^ 2 := by positivity
  have hD : -(s - x) ^ 2 / (2 * σ ^ 2) ≤
      -s ^ 2 / (2 * σ ^ 2) - (-x ^ 2 / (2 * σ ^ 2) + -(2 / σ ^ 2) * (s - x)) := by
    have h : -s ^ 2 / (2 * σ ^ 2) - (-x ^ 2 / (2 * σ ^ 2) + -(2 / σ ^ 2) * (s - x)) -
        -(s - x) ^ 2 / (2 * σ ^ 2) = (s - x) * (4 - 2 * x) / (2 * σ ^ 2) := by
      field_simp
      ring
    have h0 : 0 ≤ (s - x) * (4 - 2 * x) / (2 * σ ^ 2) :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) hσ2.le
    linarith
  have hexp : 1 - (s - x) ^ 2 / (2 * σ ^ 2) ≤
      Real.exp (-s ^ 2 / (2 * σ ^ 2) - (-x ^ 2 / (2 * σ ^ 2) + -(2 / σ ^ 2) * (s - x))) := by
    have h1 := Real.add_one_le_exp (-(s - x) ^ 2 / (2 * σ ^ 2))
    have h2 := Real.exp_le_exp.mpr hD
    have h3 : -(s - x) ^ 2 / (2 * σ ^ 2) + 1 = 1 - (s - x) ^ 2 / (2 * σ ^ 2) := by ring
    linarith
  calc Real.exp (-x ^ 2 / (2 * σ ^ 2)) *
        (Real.exp (-(2 / σ ^ 2) * (s - x)) * (1 - (s - x) ^ 2 / (2 * σ ^ 2)))
      = Real.exp (-x ^ 2 / (2 * σ ^ 2) + -(2 / σ ^ 2) * (s - x)) *
          (1 - (s - x) ^ 2 / (2 * σ ^ 2)) := by
        rw [Real.exp_add]
        ring
    _ ≤ Real.exp (-x ^ 2 / (2 * σ ^ 2) + -(2 / σ ^ 2) * (s - x)) *
          Real.exp (-s ^ 2 / (2 * σ ^ 2) - (-x ^ 2 / (2 * σ ^ 2) + -(2 / σ ^ 2) * (s - x))) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    _ = Real.exp (-s ^ 2 / (2 * σ ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- Explicit antiderivative of `e^{-(2/σ²)(u-x)} (1 - (u-x)²/(2σ²))`. -/
private theorem gs_hasDerivAt (σ x s : ℝ) (hσ : 0 < σ) :
    HasDerivAt (fun u => -(Real.exp (-(2 / σ ^ 2) * (u - x)) *
        (σ ^ 2 / 2 - σ ^ 4 / 8 - σ ^ 2 / 4 * (u - x) - (u - x) * (u - x) / 4)))
      (Real.exp (-(2 / σ ^ 2) * (s - x)) * (1 - (s - x) ^ 2 / (2 * σ ^ 2))) s := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hlin : HasDerivAt (fun u : ℝ => u - x) 1 s := (hasDerivAt_id' s).sub_const x
  have hexp : HasDerivAt (fun u => Real.exp (-(2 / σ ^ 2) * (u - x)))
      (Real.exp (-(2 / σ ^ 2) * (s - x)) * (-(2 / σ ^ 2) * 1)) s :=
    (hlin.const_mul (-(2 / σ ^ 2))).exp
  have hpoly : HasDerivAt
      (fun u => σ ^ 2 / 2 - σ ^ 4 / 8 - σ ^ 2 / 4 * (u - x) - (u - x) * (u - x) / 4)
      (0 - σ ^ 2 / 4 * 1 - (1 * (s - x) + (s - x) * 1) / 4) s :=
    ((hasDerivAt_const s (σ ^ 2 / 2 - σ ^ 4 / 8)).sub (hlin.const_mul (σ ^ 2 / 4))).sub
      ((hlin.mul hlin).div_const 4)
  refine ((hexp.mul hpoly).neg).congr_deriv ?_
  field_simp
  ring

/-- The integrated lower bound: `∫_x^{x+2} e^{-(2/σ²)(s-x)} (1 - (s-x)²/(2σ²)) ≥ σ²/2 - σ⁴/8`. -/
private theorem gs_integral_lower_ge (σ : ℝ) (hσ : 0 < σ) (x : ℝ) :
    σ ^ 2 / 2 - σ ^ 4 / 8 ≤ ∫ s in x..x + 2,
      Real.exp (-(2 / σ ^ 2) * (s - x)) * (1 - (s - x) ^ 2 / (2 * σ ^ 2)) := by
  have hcont : Continuous fun s : ℝ =>
      Real.exp (-(2 / σ ^ 2) * (s - x)) * (1 - (s - x) ^ 2 / (2 * σ ^ 2)) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x + 2)
    (fun s _ => gs_hasDerivAt σ x s hσ) (hcont.intervalIntegrable _ _)]
  simp only [add_sub_cancel_left, sub_self, mul_zero, Real.exp_zero, one_mul]
  have hE := Real.exp_pos (-(2 / σ ^ 2) * 2)
  nlinarith [mul_nonneg hE.le (show (0 : ℝ) ≤ σ ^ 4 / 8 + 1 by positivity)]

/-- **Hazard bound.** For `0 < σ ≤ 1` and every `x ≤ 2`, the density at `x` is at most
`8 / (3σ²)` times the tail mass `∫_{[x,∞)} φ`. -/
theorem density_le_hazard_mul_tail (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (x : ℝ) (hx : x ≤ 2) :
    gaussianPDFReal 0 (σ ^ 2).toNNReal x ≤
      (8 / (3 * σ ^ 2)) * ∫ t in Set.Ici x, gaussianPDFReal 0 (σ ^ 2).toNNReal t := by
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hφx : 0 ≤ gaussianPDFReal 0 (σ ^ 2).toNNReal x := gaussianPDFReal_nonneg _ _ _
  have hcont : Continuous fun s : ℝ =>
      Real.exp (-(2 / σ ^ 2) * (s - x)) * (1 - (s - x) ^ 2 / (2 * σ ^ 2)) := by
    fun_prop
  have hpt : ∀ s ∈ Set.Icc x (x + 2),
      gaussianPDFReal 0 (σ ^ 2).toNNReal x *
          (Real.exp (-(2 / σ ^ 2) * (s - x)) * (1 - (s - x) ^ 2 / (2 * σ ^ 2))) ≤
        gaussianPDFReal 0 (σ ^ 2).toNNReal s := by
    intro s hs
    rw [gs_pdf_eq σ x, gs_pdf_eq σ s]
    exact (mul_assoc _ _ _).trans_le
      (mul_le_mul_of_nonneg_left (gs_exp_shift_lower σ hσ x s hx hs.1) (by positivity))
  have h1 : gaussianPDFReal 0 (σ ^ 2).toNNReal x * (σ ^ 2 / 2 - σ ^ 4 / 8) ≤
      ∫ s in x..x + 2, gaussianPDFReal 0 (σ ^ 2).toNNReal s := by
    calc gaussianPDFReal 0 (σ ^ 2).toNNReal x * (σ ^ 2 / 2 - σ ^ 4 / 8)
        ≤ gaussianPDFReal 0 (σ ^ 2).toNNReal x * ∫ s in x..x + 2,
            Real.exp (-(2 / σ ^ 2) * (s - x)) * (1 - (s - x) ^ 2 / (2 * σ ^ 2)) :=
          mul_le_mul_of_nonneg_left (gs_integral_lower_ge σ hσ x) hφx
      _ = ∫ s in x..x + 2, gaussianPDFReal 0 (σ ^ 2).toNNReal x *
            (Real.exp (-(2 / σ ^ 2) * (s - x)) * (1 - (s - x) ^ 2 / (2 * σ ^ 2))) :=
          (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ s in x..x + 2, gaussianPDFReal 0 (σ ^ 2).toNNReal s :=
          intervalIntegral.integral_mono_on (by linarith)
            ((continuous_const.mul hcont).intervalIntegrable _ _)
            (integrable_gaussianPDFReal 0 _).intervalIntegrable hpt
  have h2 : ∫ s in x..x + 2, gaussianPDFReal 0 (σ ^ 2).toNNReal s ≤
      ∫ t in Set.Ici x, gaussianPDFReal 0 (σ ^ 2).toNNReal t := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_mono_set (integrable_gaussianPDFReal 0 _).integrableOn
      (ae_of_all _ (fun t => gaussianPDFReal_nonneg 0 _ t))
      (show Set.Ioc x (x + 2) ⊆ Set.Ici x from fun t ht => le_of_lt ht.1).eventuallyLE
  have hsq : σ ^ 2 ≤ 1 := by nlinarith
  have hσ4 : σ ^ 4 ≤ σ ^ 2 := by nlinarith
  have h3 : 3 * σ ^ 2 / 8 * gaussianPDFReal 0 (σ ^ 2).toNNReal x ≤
      ∫ t in Set.Ici x, gaussianPDFReal 0 (σ ^ 2).toNNReal t := by
    nlinarith [mul_le_mul_of_nonneg_left hσ4 hφx]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

end SmoothedSimplex.Shadow.GraphScoutHazard

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 2.4.11 (Comparing Gaussian tails)** (Spielman & Teng, arXiv:cs/0111050v7,
Lemma 2.4.11, printed p. 23, PDF p. 23). Let `σ ≤ 1` and let `µ(t) = (1/(√(2π)σ)) e^{−t²/2σ²}`.
Then, for `x ≤ 2` and `|x − y| ≤ ε`,
`∫_{t=y}^∞ µ(t) dt / ∫_{t=x}^∞ µ(t) dt ≥ 1 − 8ε/(3σ²)`.

**Formalization Note.** `σ > 0`. `µ` is the density of `gaussianReal 0 σ²`, so
`∫_{t=y}^∞ µ(t) dt = gaussianReal 0 σ² [y, ∞)`. The ratio is cross-multiplied (the denominator is
positive, so this is equivalent). -/
theorem comparing_gaussian_tails (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (x y ε : ℝ)
    (hx : x ≤ 2) (hxy : |x - y| ≤ ε) :
    (1 - 8 * ε / (3 * σ ^ 2)) * (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by
  have hv : (σ ^ 2).toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr (pow_pos hσ 2))
  have hzero : gaussianPDFReal 0 (σ ^ 2).toNNReal 0 ≤
      (8 / (3 * σ ^ 2)) * (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici 0)).toReal := by
    rw [NativeTailDensity.gaussian_mass_eq_integral (σ ^ 2).toNNReal hv (Set.Ici 0)]
    exact GraphScoutHazard.density_le_hazard_mul_tail σ hσ hσ1 0 (by norm_num)
  have hpositive : 0 < x → gaussianPDFReal 0 (σ ^ 2).toNNReal x ≤
      (8 / (3 * σ ^ 2)) * (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal := by
    intro _
    rw [NativeTailDensity.gaussian_mass_eq_integral (σ ^ 2).toNNReal hv (Set.Ici x)]
    exact GraphScoutHazard.density_le_hazard_mul_tail σ hσ hσ1 x hx
  exact NativeTailAssembly.comparison_of_zero_and_positive_hazards σ hσ x y ε hxy hzero hpositive

end SmoothedSimplex.Shadow

end Prove2SwarmSubmission

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
theorem solution (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (x y ε : ℝ)
    (hx : x ≤ 2) (hxy : |x - y| ≤ ε) :
    (1 - 8 * ε / (3 * σ ^ 2)) * (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by
  exact Prove2SwarmSubmission.SmoothedSimplex.Shadow.comparing_gaussian_tails σ hσ hσ1 x y ε hx hxy
