-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_sq_norm_mul_setIntegral_le_c926ed7b3320
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:57:11.714914+00:00
-- url     : https://prove2.me/submissions/1b3ad6d0-98c7-4506-812f-04048d8f0168

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PolydiscMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_mul_weight_eq_d36808fe1b39

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Metric Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {D : ℕ} {ρ : ℝ} {g : (Fin D → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 ρ)) {w : (Fin D → ℂ) → ℝ} (hw : Continuous w)
    (hw0 : ∀ z, 0 ≤ w z) (hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z) :
    ‖g 0‖ ^ 2 * ∫ z in closedBall (0 : Fin D → ℂ) ρ, w z ≤
      ∫ z in closedBall (0 : Fin D → ℂ) ρ, ‖g z‖ ^ 2 * w z := by
  have hmean := setIntegral_mul_weight_eq hg hw hrot
  set B := closedBall (0 : Fin D → ℂ) ρ
  have hB : IsCompact B := isCompact_closedBall 0 ρ
  have hgc : ContinuousOn g B := hg.continuousOn
  have i1 : Integrable (fun z => ‖g z‖ ^ 2 * w z) (volume.restrict B) :=
    ((hgc.norm.pow 2).mul hw.continuousOn).integrableOn_compact hB
  have i2 : Integrable w (volume.restrict B) := hw.continuousOn.integrableOn_compact hB
  have i3 : Integrable (fun z => g z * (w z : ℂ)) (volume.restrict B) :=
    (hgc.mul (Complex.continuous_ofReal.comp hw).continuousOn).integrableOn_compact hB
  have key : 0 ≤ ∫ z in B, ‖g z - g 0‖ ^ 2 * w z :=
    setIntegral_nonneg measurableSet_closedBall (fun z _ => mul_nonneg (sq_nonneg _) (hw0 z))
  have expand : ∀ z, ‖g z - g 0‖ ^ 2 * w z = (‖g z‖ ^ 2 * w z + ‖g 0‖ ^ 2 * w z) -
      2 * Complex.reCLM (g z * (w z : ℂ) * (starRingEnd ℂ) (g 0)) := by
    intro z
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_sub]
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [expand] at key
  have i4 : Integrable (fun z => g z * (w z : ℂ) * (starRingEnd ℂ) (g 0)) (volume.restrict B) :=
    i3.mul_const _
  rw [integral_sub (f := fun z => ‖g z‖ ^ 2 * w z + ‖g 0‖ ^ 2 * w z)
      (g := fun z => 2 * Complex.reCLM (g z * (w z : ℂ) * (starRingEnd ℂ) (g 0)))
      (i1.add (i2.const_mul _)) ((Complex.reCLM.integrable_comp i4).const_mul 2),
    integral_add (f := fun z => ‖g z‖ ^ 2 * w z) (g := fun z => ‖g 0‖ ^ 2 * w z) i1
      (i2.const_mul _), integral_const_mul, integral_const_mul,
    Complex.reCLM.integral_comp_comm i4, integral_mul_const, hmean, integral_complex_ofReal] at key
  have hre : Complex.reCLM (g 0 * ((∫ z in B, w z : ℝ) : ℂ) * (starRingEnd ℂ) (g 0)) =
      ‖g 0‖ ^ 2 * ∫ z in B, w z := by
    rw [mul_comm (g 0), mul_assoc, Complex.mul_conj, Complex.reCLM_apply, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.sq_norm, mul_comm]
  rw [hre] at key
  linarith
end GroundTheory.Heights₂.Heights.HilbertSamuel
