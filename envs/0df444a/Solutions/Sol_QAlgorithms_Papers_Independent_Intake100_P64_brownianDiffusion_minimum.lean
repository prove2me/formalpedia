-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.brownianDiffusion_minimum
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:33:48.819706+00:00
-- url     : https://prove2.me/submissions/67d5fa49-f8ab-4b45-8df5-b6f2add10f0b

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64
import Definitions.Def_LevyStochCalc_Probability_GaussianMoments_F000

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

open ProbabilityTheory in
theorem AuxBDM_sq (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ y : ℝ, y ^ 2 * gaussianPDFReal 0 v y = v := by
  have h := LevyStochCalc.Probability.integral_pow_even_gaussianReal (v := v) 1
  rw [integral_gaussianReal_eq_integral_smul hv] at h
  simp only [smul_eq_mul, mul_one, pow_one] at h
  norm_num at h
  rw [← h]; congr 1; funext y; ring

open ProbabilityTheory in
theorem AuxBDM_int_sq (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (fun y : ℝ => y ^ 2 * gaussianPDFReal 0 v y) := by
  have hv' : (0 : ℝ) < v := by positivity
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := (2 * (v : ℝ))⁻¹) (by positivity)
    (s := 2) (by norm_num)).const_mul (Real.sqrt (2 * Real.pi * v))⁻¹
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [gaussianPDFReal_def, sub_zero]
  rw [show (y : ℝ) ^ (2 : ℝ) = y ^ 2 by norm_cast]
  have e : -(2 * (v : ℝ))⁻¹ * y ^ 2 = -y ^ 2 / (2 * v) := by ring
  rw [e]; ring

open ProbabilityTheory in
theorem AuxBDM_maxwell (M beta : ℝ) (hM : 0 < M) (hbeta : 0 < beta) :
    ∫ P : Momentum, ‖P‖ ^ 2 * maxwell M beta P = 3 * (M / beta) := by
  set v : ℝ≥0 := (M / beta).toNNReal with hvdef
  have hvr : (v : ℝ) = M / beta := Real.coe_toNNReal _ (by positivity)
  have hv0 : v ≠ 0 := by
    intro h; have : (v : ℝ) = 0 := by simp [h]
    rw [hvr] at this; have : 0 < M / beta := by positivity
    linarith
  set f : ℝ → ℝ := gaussianPDFReal 0 v
  set h : Fin 3 → Fin 3 → ℝ → ℝ := fun i j y => if j = i then y ^ 2 * f y else f y
  have key : ∀ x : Fin 3 → ℝ, ‖(WithLp.toLp 2 x : Momentum)‖ ^ 2 * maxwell M beta (WithLp.toLp 2 x)
      = ∑ i, ∏ j, h i j (x j) := by
    intro x
    have hn : ‖(WithLp.toLp 2 x : Momentum)‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_three]
    have hw : (beta / (2 * Real.pi * M)) ^ (3 / 2 : ℝ) =
        ((Real.sqrt (2 * Real.pi * v))⁻¹) ^ 3 := by
      rw [hvr, ← Real.sqrt_inv, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul
        (by positivity)]
      congr 1
      · field_simp
      · norm_num
    simp only [maxwell, h, f, gaussianPDFReal_def, Fin.sum_univ_three, Fin.prod_univ_three]
    rw [Real.rpow_eq_pow] at *
    rw [hw, hn]
    simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq, sub_zero]
    have e : Real.exp (-beta * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) / (2 * M)) =
        Real.exp (-x 0 ^ 2 / (2 * v)) * Real.exp (-x 1 ^ 2 / (2 * v)) *
          Real.exp (-x 2 ^ 2 / (2 * v)) := by
      rw [← Real.exp_add, ← Real.exp_add, hvr]; congr 1; field_simp; ring
    rw [e]; ring
  have hint : ∀ i j, Integrable (h i j) := by
    intro i j
    by_cases hij : j = i
    · simpa [h, hij] using AuxBDM_int_sq v hv0
    · simpa [h, hij, f] using integrable_gaussianPDFReal (0 : ℝ) v
  have hI : ∀ i j, ∫ y, h i j y = if j = i then (v : ℝ) else 1 := by
    intro i j
    by_cases hij : j = i
    · simp [h, hij, f, AuxBDM_sq v hv0]
    · simp [h, hij, f, integral_gaussianPDFReal_eq_one 0 hv0]
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).map_eq, ← MeasurableEquiv.coe_toLp,
    integral_map_equiv]
  simp only [MeasurableEquiv.coe_toLp]
  simp_rw [key]
  rw [integral_finsetSum _ (fun i _ => by
    rw [volume_pi]; exact Integrable.fintype_prod (hint i))]
  simp_rw [volume_pi, integral_fintype_prod_eq_prod, hI]
  simp [Fin.sum_univ_three, Fin.prod_univ_three, hvr]

theorem _root_.solution (M beta hbar eta : ℝ)
    (hM : 0 < M) (hbeta : 0 < beta) (hhbar : 0 < hbar) (heta : 0 ≤ eta) :
    positionDiffusion M beta hbar eta = (beta * hbar / (4 * M)) ^ 2 * momentumDiffusion M beta eta ∧
    positionDiffusion M beta hbar eta * momentumDiffusion M beta eta = eta ^ 2 * hbar ^ 2 / 16 ∧
    momentumDiffusion M beta eta = eta / 3 *
      (∫ P : Momentum, ‖P‖ ^ 2 * maxwell M beta P) ∧
    positionDiffusion M beta hbar eta = eta / (32 * Real.pi) *
      Real.sqrt (2 * Real.pi * hbar ^ 2 * beta / M) ^ 2 ∧
    0 ≤ positionDiffusion M beta hbar eta ∧
    (∀ Dxx : ℝ, 0 ≤ Dxx →
      eta ^ 2 * hbar ^ 2 / 16 ≤ Dxx * momentumDiffusion M beta eta →
      positionDiffusion M beta hbar eta ≤ Dxx) := by
  simp only [positionDiffusion, momentumDiffusion]
  refine ⟨by field_simp <;> ring, by field_simp <;> ring, ?_, ?_, by positivity, ?_⟩
  · rw [AuxBDM_maxwell M beta hM hbeta]; field_simp
  · rw [Real.sq_sqrt (by positivity)]; field_simp; ring
  · intro D hD hle
    rcases heta.eq_or_lt with h0 | hpos
    · subst h0; simp [hD]
    · have hk : 0 < eta * M / beta := by positivity
      refine le_of_mul_le_mul_right ?_ hk
      calc eta * beta * hbar ^ 2 / (16 * M) * (eta * M / beta) = eta ^ 2 * hbar ^ 2 / 16 := by
            field_simp
        _ ≤ D * (eta * M / beta) := hle

end QAlgorithms.Papers.Independent.Intake100.P64

end
