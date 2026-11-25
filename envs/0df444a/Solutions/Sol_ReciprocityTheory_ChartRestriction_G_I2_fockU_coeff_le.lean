-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.fockU_coeff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:01:43.954809+00:00
-- url     : https://prove2.me/submissions/afa3c62a-f0c1-4565-9474-eb7a3f5c0b1c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegralMulConjGaussianEqCoeffNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_mul_le_sqrt_mul_sqrt_mul_avg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fockInner_self_re_eq_coeffNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_card_support_le_and_sum_two_pow_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_coeffNormSq_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_monomialKernel_mul_gaussian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_monomialKernel_mul_gaussian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integral_monomialKernel_mul_gaussian_half
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_monomialKernel_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_norm_eval_sq_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g c : ℕ} (a : EuclideanSpace ℂ (Fin g)) (F G : EuclideanSpace ℂ (Fin g) → ℂ)
    (hF : IsPolyLE c F) (hG : IsPolyLE c G) :
    ‖fockIP (fockU a F) G‖ ≤ 2 ^ (1 + 3 * ((g : ℝ) + c) / 2) * Real.exp (-‖a‖ ^ 2 / 16) *
      Real.sqrt (fockIP F F).re * Real.sqrt (fockIP G G).re := by
  obtain ⟨p, hpc, hp⟩ := hF
  obtain ⟨q, hqc, hq⟩ := hG
  rw [fockInner_self_re_eq_coeffNormSq p F hp, fockInner_self_re_eq_coeffNormSq q G hq]
  have hNF := coeffNormSq_nonneg p
  have hNG := coeffNormSq_nonneg q

  have hre : ∀ z : EuclideanSpace ℂ (Fin g), (∑ i, z i * (starRingEnd ℂ) (a i)).re =
      (‖z‖ ^ 2 + ‖a‖ ^ 2 - ‖z - a‖ ^ 2) / 2 := by
    intro z
    have h1 : (∑ i, z i * (starRingEnd ℂ) (a i)) = inner ℂ a z := by
      simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    have h2 := norm_sub_sq (𝕜 := ℂ) z a
    have h3 := inner_re_symm (𝕜 := ℂ) z a
    simp only [RCLike.re_to_complex] at h2 h3
    rw [h1]
    linarith
  have hI : ∀ z : EuclideanSpace ℂ (Fin g),
      ‖fockU a F z * (starRingEnd ℂ) (G z) * ((Real.exp (-‖z‖ ^ 2) : ℝ) : ℂ)‖ =
        ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) := by
    intro z
    simp only [fockU, norm_mul, Complex.norm_exp, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Complex.sub_re, Complex.ofReal_re, hre z]
    have e : Real.exp ((‖z‖ ^ 2 + ‖a‖ ^ 2 - ‖z - a‖ ^ 2) / 2 - ‖a‖ ^ 2 / 2) *
        Real.exp (-‖z‖ ^ 2) = Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← e]
    ring
  have hmain : ∀ M : EuclideanSpace ℂ (Fin g) → ℝ, Integrable M →
      (∀ z, ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) ≤ M z) →
      ‖fockIP (fockU a F) G‖ ≤ (Real.pi ^ g)⁻¹ * ∫ z, M z := by
    intro M hM hle
    unfold fockIP
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hM
      (Filter.Eventually.of_forall fun z => (hI z).le.trans (hle z))) (by positivity)
  have hexp2 : ∀ x : ℝ, Real.exp (x / 2) ^ 2 = Real.exp x := by
    intro x
    rw [sq, ← Real.exp_add]
    ring_nf
  have hs : 0 ≤ Real.sqrt (fa1N p) * Real.sqrt (fa1N q) := by positivity
  obtain ⟨hcp, hsp⟩ := card_support_le_and_sum_two_pow_le p hpc
  obtain ⟨hcq, hsq⟩ := card_support_le_and_sum_two_pow_le q hqc
  have hi1p : Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K p z * Real.exp (-‖z‖ ^ 2)) := by
    simpa using integrable_monomialKernel_mul_gaussian p (b := 1) one_pos
  have hi1q : Integrable (fun z : EuclideanSpace ℂ (Fin g) => fa1K q z * Real.exp (-‖z‖ ^ 2)) := by
    simpa using integrable_monomialKernel_mul_gaussian q (b := 1) one_pos
  have hi2p : Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := integrable_monomialKernel_mul_gaussian p (by norm_num)
  have hi2q : Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
      fa1K q z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := integrable_monomialKernel_mul_gaussian q (by norm_num)

  have hB1 : ‖fockIP (fockU a F) G‖ ≤
      Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * 2 ^ (g + c) := by
    have hM : Integrable (fun z : EuclideanSpace ℂ (Fin g) =>
        Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * ((fa1K p (z - a) * Real.exp (-‖z - a‖ ^ 2) +
          fa1K q z * Real.exp (-‖z‖ ^ 2)) / 2)) :=
      (((hi1p.comp_sub_right a).add hi1q).div_const 2).const_mul _
    refine (hmain _ hM (fun z => ?_)).trans ?_
    · have hu : (‖F (z - a)‖ * Real.exp (-‖z - a‖ ^ 2 / 2)) ^ 2 ≤
          fa1N p * (fa1K p (z - a) * Real.exp (-‖z - a‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hp]; exact norm_eval_sq_le p (z - a)) (Real.exp_pos _).le
      have hv : (‖G z‖ * Real.exp (-‖z‖ ^ 2 / 2)) ^ 2 ≤
          fa1N q * (fa1K q z * Real.exp (-‖z‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hq]; exact norm_eval_sq_le q z) (Real.exp_pos _).le
      have hab := mul_le_sqrt_mul_sqrt_mul_avg (by positivity) hNF hNG
        (mul_nonneg (monomialKernel_nonneg p _) (Real.exp_pos _).le)
        (mul_nonneg (monomialKernel_nonneg q _) (Real.exp_pos _).le) one_pos hu hv
      calc ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2)
          = (‖F (z - a)‖ * Real.exp (-‖z - a‖ ^ 2 / 2)) * (‖G z‖ * Real.exp (-‖z‖ ^ 2 / 2)) := by
            rw [show -‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2 = -‖z - a‖ ^ 2 / 2 + -‖z‖ ^ 2 / 2 by ring,
              Real.exp_add]
            ring
        _ ≤ _ := hab
        _ = _ := by ring
    · have hT : ∫ z : EuclideanSpace ℂ (Fin g), fa1K p (z - a) * Real.exp (-‖z - a‖ ^ 2) =
          ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-‖z‖ ^ 2) :=
        integral_sub_right_eq_self (fun z => fa1K p z * Real.exp (-‖z‖ ^ 2)) a
      rw [integral_const_mul, integral_div, integral_add (hi1p.comp_sub_right a) hi1q, hT,
        integral_monomialKernel_mul_gaussian, integral_monomialKernel_mul_gaussian]
      have hpi : 0 < Real.pi ^ g := by positivity
      have e : (Real.pi ^ g)⁻¹ * (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
          ((Real.pi ^ g * p.support.card + Real.pi ^ g * q.support.card) / 2)) =
          Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * ((p.support.card + q.support.card) / 2) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) hs

  have hB2 : ‖fockIP (fockU a F) G‖ ≤ Real.exp (-‖a‖ ^ 2 / 8) *
      (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * (2 ^ (g + c) * 2 ^ (g + c))) := by
    have hM : Integrable (fun z : EuclideanSpace ℂ (Fin g) => Real.exp (-‖a‖ ^ 2 / 8) *
        (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
          ((fa1K p (z - a) * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2) +
            fa1K q z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) / 2))) :=
      ((((hi2p.comp_sub_right a).add hi2q).div_const 2).const_mul _).const_mul _
    refine (hmain _ hM (fun z => ?_)).trans ?_
    · have hu : (‖F (z - a)‖ * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2)) ^ 2 ≤
          fa1N p * (fa1K p (z - a) * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hp]; exact norm_eval_sq_le p (z - a)) (Real.exp_pos _).le
      have hv : (‖G z‖ * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2)) ^ 2 ≤
          fa1N q * (fa1K q z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) := by
        rw [mul_pow, hexp2, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by rw [hq]; exact norm_eval_sq_le q z) (Real.exp_pos _).le
      have hab := mul_le_sqrt_mul_sqrt_mul_avg (by positivity) hNF hNG
        (mul_nonneg (monomialKernel_nonneg p _) (Real.exp_pos _).le)
        (mul_nonneg (monomialKernel_nonneg q _) (Real.exp_pos _).le) one_pos hu hv
      have hpar : ‖a‖ ^ 2 ≤ 2 * (‖z - a‖ ^ 2 + ‖z‖ ^ 2) := by
        have h := norm_sub_le z (z - a)
        rw [sub_sub_cancel] at h
        nlinarith [norm_nonneg a, norm_nonneg z, norm_nonneg (z - a), sq_nonneg (‖z‖ - ‖z - a‖)]
      have hexpb : Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2) ≤ Real.exp (-‖a‖ ^ 2 / 8) *
          (Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2) * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith)
      calc ‖F (z - a)‖ * ‖G z‖ * Real.exp (-‖z - a‖ ^ 2 / 2 - ‖z‖ ^ 2 / 2)
          ≤ ‖F (z - a)‖ * ‖G z‖ * (Real.exp (-‖a‖ ^ 2 / 8) *
            (Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2) * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2))) :=
            mul_le_mul_of_nonneg_left hexpb (by positivity)
        _ = Real.exp (-‖a‖ ^ 2 / 8) * ((‖F (z - a)‖ * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2 / 2)) *
            (‖G z‖ * Real.exp (-(1 / 2) * ‖z‖ ^ 2 / 2))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hab (Real.exp_pos _).le
        _ = _ := by ring
    · have hT : ∫ z : EuclideanSpace ℂ (Fin g), fa1K p (z - a) * Real.exp (-(1 / 2) * ‖z - a‖ ^ 2) =
          ∫ z : EuclideanSpace ℂ (Fin g), fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2) :=
        integral_sub_right_eq_self (fun z => fa1K p z * Real.exp (-(1 / 2) * ‖z‖ ^ 2)) a
      rw [integral_const_mul, integral_const_mul, integral_div,
        integral_add (hi2p.comp_sub_right a) hi2q, hT, integral_monomialKernel_mul_gaussian_half, integral_monomialKernel_mul_gaussian_half]
      have hpi : 0 < Real.pi ^ g := by positivity
      have e : (Real.pi ^ g)⁻¹ * (Real.exp (-‖a‖ ^ 2 / 8) * (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
          ((Real.pi ^ g * ∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) +
            Real.pi ^ g * ∑ α ∈ q.support, (2 : ℝ) ^ (g + ∑ i, α i)) / 2))) =
          Real.exp (-‖a‖ ^ 2 / 8) * (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) *
            ((∑ α ∈ p.support, (2 : ℝ) ^ (g + ∑ i, α i) +
              ∑ α ∈ q.support, (2 : ℝ) ^ (g + ∑ i, α i)) / 2)) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hs)
        (Real.exp_pos _).le

  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (2 : ℝ) ^ (((g : ℝ) + c) / 2) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by
    rw [hy]
    positivity
  have hyT : y ^ 2 = (2 : ℝ) ^ (g + c) := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      show ((g : ℝ) + c) / 2 * ((2 : ℕ) : ℝ) = ((g + c : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hR : (2 : ℝ) ^ (1 + 3 * ((g : ℝ) + c) / 2) = 2 * y ^ 3 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_one, show 3 * ((g : ℝ) + c) / 2 = ((g : ℝ) + c) / 2 * ((3 : ℕ) : ℝ) by push_cast; ring]
  have hE : Real.exp (-‖a‖ ^ 2 / 16) ^ 2 = Real.exp (-‖a‖ ^ 2 / 8) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hX0 := norm_nonneg (fockIP (fockU a F) G)
  rw [hR]
  have key : ‖fockIP (fockU a F) G‖ ^ 2 ≤ (2 * y ^ 3 * Real.exp (-‖a‖ ^ 2 / 16) *
      Real.sqrt (fa1N p) * Real.sqrt (fa1N q)) ^ 2 := by
    have h12 := mul_le_mul hB1 hB2 hX0 (by positivity)
    have e1 : Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * 2 ^ (g + c) * (Real.exp (-‖a‖ ^ 2 / 8) *
        (Real.sqrt (fa1N p) * Real.sqrt (fa1N q) * (2 ^ (g + c) * 2 ^ (g + c)))) =
        Real.sqrt (fa1N p) ^ 2 * Real.sqrt (fa1N q) ^ 2 * y ^ 6 * Real.exp (-‖a‖ ^ 2 / 8) := by
      rw [← hyT]
      ring
    have e2 : (2 * y ^ 3 * Real.exp (-‖a‖ ^ 2 / 16) * Real.sqrt (fa1N p) * Real.sqrt (fa1N q)) ^ 2 =
        4 * (Real.sqrt (fa1N p) ^ 2 * Real.sqrt (fa1N q) ^ 2 * y ^ 6 * Real.exp (-‖a‖ ^ 2 / 8)) := by
      rw [← hE]
      ring
    rw [sq, e2]
    rw [e1] at h12
    have : 0 ≤ Real.sqrt (fa1N p) ^ 2 * Real.sqrt (fa1N q) ^ 2 * y ^ 6 * Real.exp (-‖a‖ ^ 2 / 8) := by
      positivity
    linarith
  exact (pow_le_pow_iff_left₀ hX0 (by positivity) two_ne_zero).1 key
end ReciprocityTheory.ChartRestriction.G.I2
