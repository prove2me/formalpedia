-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_setLIntegral_rot_7dac8de6a7df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:03:38.166325+00:00
-- url     : https://prove2.me/submissions/9cd4b7e7-704e-4adb-8b1b-a9e6b0eda5a1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution {V : Type*} [MeasurableSpace V] (μ : Measure V) [SFinite μ]
    (S : Set V) (hS : MeasurableSet S) (R : ℝ → V → V) (hR : Measurable (Function.uncurry R))
    (hpres : ∀ θ, MeasurePreserving (R θ) μ μ) (hinv : ∀ θ, R θ ⁻¹' S = S)
    (G : V → ENNReal) (hG : Measurable G) :
    ENNReal.ofReal (2 * Real.pi) * ∫⁻ u in S, G u ∂μ =
      ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi), G (R θ u)) ∂μ := by
  have h1 : ∀ θ, ∫⁻ u in S, G (R θ u) ∂μ = ∫⁻ u in S, G u ∂μ := by
    intro θ
    have := (hpres θ).setLIntegral_comp_preimage hS hG
    rwa [hinv θ] at this
  rw [lintegral_lintegral_swap]
  · simp_rw [h1]
    rw [setLIntegral_const]
    simp [Real.volume_Ioc, mul_comm]
  · exact (hG.comp (hR.comp measurable_swap)).aemeasurable
end GroundTheory.Heights₂.Heights.LogInt
