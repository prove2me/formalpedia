-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.refractiveIndex_diluteExpansion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yivy Yu
-- created : 2026-11-21T02:24:32.711375+00:00
-- url     : https://prove2.me/submissions/18c0348d-3bdf-4186-8b3b-082ba69fc319
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64
import Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P64_optical_forwardLoss

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P64

private theorem complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  simp [Complex.sqrt]

private theorem complex_sqrt_re_nonneg (z : ℂ) : 0 ≤ (Complex.sqrt z).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  positivity

/-- A global quadratic remainder bound for the principal square root at one. -/
private theorem sqrt_linear_error (z : ℂ) :
    ‖Complex.sqrt (1 + z) - (1 + z / 2)‖ ≤ ‖z‖ ^ 2 / 2 := by
  let w := Complex.sqrt (1 + z)
  have hw : w ^ 2 = 1 + z := complex_sqrt_sq _
  have hre : 0 ≤ w.re := complex_sqrt_re_nonneg _
  have hden : 1 ≤ ‖w + 1‖ := by
    calc
      1 ≤ (w + 1).re := by simpa using hre
      _ ≤ ‖w + 1‖ := Complex.re_le_norm _
  have hmul : (w - 1) * (w + 1) = z := by calc
    _ = w ^ 2 - 1 := by ring
    _ = z := by rw [hw]; ring
  have hsmall : ‖w - 1‖ ≤ ‖z‖ := by
    calc
      ‖w - 1‖ ≤ ‖w - 1‖ * ‖w + 1‖ := le_mul_of_one_le_right (norm_nonneg _) hden
      _ = ‖z‖ := by rw [← norm_mul, hmul]
  have herr : w - (1 + z / 2) = -(w - 1) ^ 2 / 2 := by
    linear_combination (1 / 2 : ℂ) * hw
  change ‖w - (1 + z / 2)‖ ≤ _
  rw [herr, norm_div, norm_neg, norm_pow]
  norm_num
  nlinarith [sq_le_sq₀ (norm_nonneg (w - 1)) (norm_nonneg z) |>.mpr hsmall]

/-- The index is the principal square root of one plus twice the density times its slope. -/
private theorem refractiveIndex_formula (d : CollisionData) (K : Momentum) (n : ℝ) :
    refractiveIndex d K n = Complex.sqrt (1 + 2 * (n : ℂ) * refractiveSlope d K) := by
  unfold refractiveIndex refractiveSlope
  congr 2
  push_cast
  ring

/-- The physical dilute-gas coefficient has a controlled quadratic error. -/
private theorem refractiveIndex_quadratic_error (d : CollisionData) (K : Momentum) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ ∀ n : ℝ, 0 ≤ n → n ≤ delta →
      ‖refractiveIndex d K n - (1 + (n : ℂ) * refractiveSlope d K)‖ ≤ C * n ^ 2 := by
  refine ⟨2 * ‖refractiveSlope d K‖ ^ 2 + 1, 1, by positivity, by norm_num, ?_⟩
  intro n hn _
  have h := sqrt_linear_error (2 * (n : ℂ) * refractiveSlope d K)
  have hs : 1 + (2 * (n : ℂ) * refractiveSlope d K) / 2 =
      1 + (n : ℂ) * refractiveSlope d K := by ring
  rw [hs, ← refractiveIndex_formula, norm_mul, norm_mul] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn] at h
  norm_num at h
  nlinarith [sq_nonneg n]

private theorem refractiveIndex_squared (d : CollisionData) (K : Momentum) (hK : K ≠ 0)
    (n : ℝ) :
    refractiveIndex d K n ^ 2 =
      1 - (n / d.parameters.density : ℝ) * opticalPotential d (d.parameters.hbar • K) /
        (‖d.parameters.hbar • K‖ ^ 2 / (2 * d.parameters.M) : ℝ) := by
  have hM : d.parameters.M ≠ 0 := ne_of_gt d.parameters.M_pos
  have hbar : d.parameters.hbar ≠ 0 := ne_of_gt d.parameters.hbar_pos
  have hdensity : d.parameters.density ≠ 0 := ne_of_gt d.parameters.density_pos
  have hred : reducedMass d.parameters ≠ 0 := by
    unfold reducedMass
    exact ne_of_gt (div_pos (mul_pos d.parameters.m_pos d.parameters.M_pos)
      (add_pos d.parameters.m_pos d.parameters.M_pos))
  have hnorm : ‖K‖ ≠ 0 := norm_ne_zero_iff.mpr hK
  simp only [refractiveIndex, complex_sqrt_sq, opticalPotential, norm_smul,
    Real.norm_eq_abs, abs_of_pos d.parameters.hbar_pos]
  push_cast
  field_simp [hM, hbar, hdensity, hred, hnorm]
  ring

private theorem refractiveIndex_attenuation (d : CollisionData) (K : Momentum) (L n : ℝ) :
    ‖Complex.exp (Complex.I * refractiveIndex d K n * (‖K‖ * L : ℝ))‖ ^ 2 =
      Real.exp (-2 * (refractiveIndex d K n).im * ‖K‖ * L) := by
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem refractiveSlope_im_of_loss (d : CollisionData) (F : TransverseFrames)
    (K : Momentum) (hK : K ≠ 0)
    (hloss : collisionLossRate d F (d.parameters.hbar • K) =
      4 * Real.pi * d.parameters.hbar * d.parameters.density /
        reducedMass d.parameters * (forwardAverage d (d.parameters.hbar • K)).im) :
    d.parameters.density * (refractiveSlope d K).im =
      collisionLossRate d F (d.parameters.hbar • K) * d.parameters.M /
        (2 * d.parameters.hbar * ‖K‖ ^ 2) := by
  have hbar : d.parameters.hbar ≠ 0 := ne_of_gt d.parameters.hbar_pos
  have hred : reducedMass d.parameters ≠ 0 := by
    unfold reducedMass
    exact ne_of_gt (div_pos (mul_pos d.parameters.m_pos d.parameters.M_pos)
      (add_pos d.parameters.m_pos d.parameters.M_pos))
  have hnorm : ‖K‖ ≠ 0 := norm_ne_zero_iff.mpr hK
  simp only [refractiveSlope, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]
  rw [hloss]
  field_simp [hbar, hred, hnorm]
  ring

private theorem attenuation_exponent_of_loss (d : CollisionData) (F : TransverseFrames)
    (K : Momentum) (hK : K ≠ 0) (L : ℝ)
    (him : d.parameters.density * (refractiveSlope d K).im =
      collisionLossRate d F (d.parameters.hbar • K) * d.parameters.M /
        (2 * d.parameters.hbar * ‖K‖ ^ 2)) :
    2 * (d.parameters.density * (refractiveSlope d K).im) * ‖K‖ * L =
      collisionLossRate d F (d.parameters.hbar • K) * L /
        (d.parameters.hbar * ‖K‖ / d.parameters.M) := by
  have hM : d.parameters.M ≠ 0 := ne_of_gt d.parameters.M_pos
  have hbar : d.parameters.hbar ≠ 0 := ne_of_gt d.parameters.hbar_pos
  have hnorm : ‖K‖ ≠ 0 := norm_ne_zero_iff.mpr hK
  rw [him]
  field_simp [hM, hbar, hnorm]

end QAlgorithms.Papers.Independent.Intake100.P64

open QAlgorithms.Papers.Independent.Intake100.P64

/-- Reduction to the existing microscopic optical-theorem milestone. -/
theorem solution (d : CollisionData) (F : TransverseFrames)
    (K : Momentum) (hK : K ≠ 0) (L : ℝ) (_hL : 0 ≤ L)
    (hoptical : OpticalDomain d F (d.parameters.hbar • K)) :
    (∀ n : ℝ, refractiveIndex d K n ^ 2 =
      1 - (n / d.parameters.density : ℝ) * opticalPotential d (d.parameters.hbar • K) /
        (‖d.parameters.hbar • K‖ ^ 2 / (2 * d.parameters.M) : ℝ)) ∧
    (∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ ∀ n : ℝ, 0 ≤ n → n ≤ delta →
      ‖refractiveIndex d K n - (1 + (n : ℂ) * refractiveSlope d K)‖ ≤ C * n ^ 2) ∧
    d.parameters.density * (refractiveSlope d K).im =
      collisionLossRate d F (d.parameters.hbar • K) * d.parameters.M /
        (2 * d.parameters.hbar * ‖K‖ ^ 2) ∧
    2 * (d.parameters.density * (refractiveSlope d K).im) * ‖K‖ * L =
      collisionLossRate d F (d.parameters.hbar • K) * L / (d.parameters.hbar * ‖K‖ / d.parameters.M) ∧
    (∀ n : ℝ, ‖Complex.exp (Complex.I * refractiveIndex d K n * (‖K‖ * L : ℝ))‖ ^ 2 =
      Real.exp (-2 * (refractiveIndex d K n).im * ‖K‖ * L)) := by
  have hloss := (optical_forwardLoss d F (d.parameters.hbar • K) hoptical).2.1
  have him := refractiveSlope_im_of_loss d F K hK hloss
  exact ⟨refractiveIndex_squared d K hK, refractiveIndex_quadratic_error d K,
    him, attenuation_exponent_of_loss d F K hK L him, refractiveIndex_attenuation d K L⟩

end
