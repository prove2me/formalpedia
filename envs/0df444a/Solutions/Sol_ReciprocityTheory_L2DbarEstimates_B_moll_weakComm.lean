-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.B.moll_weakComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:19.916183+00:00
-- url     : https://prove2.me/submissions/09b9fd53-4a70-4bee-8a28-675917401266

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_HasCompactSupport
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_FderivMollApply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_B_fderiv_moll_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.B
open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise
namespace ReciprocityTheory.L2DbarEstimates.B
theorem _root_.solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : WeakCommSt E μ := by
  intro m c v g w hw K
  funext x
  have hd : ∀ k, fderiv ℝ (moll K (g k)) x (v k) =
      ∫ y, (fderiv ℝ K.toFun (x - y) (v k)) • g k y ∂μ :=
    fun k => fderiv_moll_apply E μ K (hw.1 k) x (v k)
  set φ : E → ℂ := fun y => ((K.toFun (x - y) : ℝ) : ℂ) with hφdef
  have hφs : ContDiff ℝ ∞ φ :=
    Complex.ofRealCLM.contDiff.comp (K.smooth.comp (contDiff_const.sub contDiff_id))
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall x K.r) fun y hy => by
      simp only [hφdef, Complex.ofReal_eq_zero]
      by_contra h
      apply hy
      have h' := K.support_subset h
      rw [mem_ball_zero_iff] at h'
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact h'.le
  have hw3 := hw.2.2 φ hφs hφc
  have hdφ : ∀ y a, fderiv ℝ φ y a = -((fderiv ℝ K.toFun (x - y) a : ℝ) : ℂ) := by
    intro y a
    have h1 : HasFDerivAt (fun y : E => x - y) (-ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((K.smooth.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y h2
    rw [(show HasFDerivAt φ _ y from h3).fderiv]
    simp
  have hm : moll K w x = ∫ y, w y * φ y ∂μ := by
    show ∫ t, K.toFun t • w (x - t) ∂μ = _
    rw [← integral_sub_left_eq_self (fun t => K.toFun t • w (x - t)) μ x]
    congr 1
    ext y
    simp only [hφdef, sub_sub_cancel, Complex.real_smul]
    ring
  simp only [Dop, hd]
  rw [hm, hw3, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_neg, ← integral_neg]
  congr 2
  ext y
  rw [hdφ, Complex.real_smul]
  ring
end ReciprocityTheory.L2DbarEstimates.B
