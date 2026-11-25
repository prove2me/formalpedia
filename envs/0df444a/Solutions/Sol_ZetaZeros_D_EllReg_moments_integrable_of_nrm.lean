-- Prove2me | solution 1 for ZetaZeros.D.EllReg.moments_integrable_of_nrm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:10:06.776939+00:00
-- url     : https://prove2.me/submissions/3111b352-1511-457d-a2c2-7a83576507a0

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_Moments

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
namespace ZetaZeros.D.EllReg
theorem _root_.solution {d : ℕ} (F : E d → ℂ) (hF : Continuous F)
    (h : ∀ s : ℕ, nrm (s : ℝ) 0 0 F < ⊤) (n : ℕ) :
    Integrable (fun v : E d => ‖v‖ ^ n * ‖F v‖) := by
  set m : ℕ := n + (d + 1) with hm
  let A : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ m * ‖F v‖ ^ 2
  let B : E d → ℝ := fun v => (1 + ‖v‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)
  have hAm : Continuous A := by
    have : Continuous fun v : E d => (1 + ‖v‖ ^ 2) := by fun_prop
    exact (this.pow m).mul ((continuous_norm.comp hF).pow 2)
  have hA : Integrable A := by
    refine ⟨hAm.aestronglyMeasurable, ?_⟩
    have hs := h m
    unfold nrm om at hs
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (lintegral_mono fun v => le_of_eq ?_) hs
    have ht0 : (0 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by positivity
    rw [Real.enorm_eq_ofReal (by positivity), ← ofReal_norm, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [A]
    congr 1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, add_zero, zero_div, neg_zero,
      Real.rpow_zero, mul_one]
    rw [← Real.rpow_natCast ((1 + ‖v‖ ^ 2) ^ ((m : ℝ) / 2)), ← Real.rpow_mul ht0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hB : Integrable B := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [finrank_euclideanSpace_fin]
    linarith
  refine (hA.add hB).mono' ((continuous_norm.pow n).mul (continuous_norm.comp hF)).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun v => ?_)
  have ht1 : (1 : ℝ) ≤ 1 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg ‖v‖]
  have ht0 : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by linarith
  have hBv : B v = ((1 + ‖v‖ ^ 2) ^ (d + 1))⁻¹ := by
    simp only [B]
    rw [show -(2 * ((d : ℝ) + 1)) / 2 = -(((d + 1 : ℕ) : ℝ)) by push_cast; ring, Real.rpow_neg ht0.le,
      Real.rpow_natCast]
  have hAB : A v * B v = (1 + ‖v‖ ^ 2) ^ n * ‖F v‖ ^ 2 := by
    rw [hBv]
    simp only [A, hm, pow_add]
    field_simp
  have hx : (‖v‖ ^ n * ‖F v‖) ^ 2 ≤ A v * B v := by
    rw [hAB, mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
    gcongr
    linarith
  have hA0 : 0 ≤ A v := by positivity
  have hB0 : 0 ≤ B v := by simp only [B]; positivity
  have hx0 : 0 ≤ ‖v‖ ^ n * ‖F v‖ := by positivity
  rw [Real.norm_of_nonneg hx0]
  show ‖v‖ ^ n * ‖F v‖ ≤ A v + B v
  nlinarith [sq_nonneg (A v - B v), mul_nonneg hA0 hB0]
end ZetaZeros.D.EllReg
