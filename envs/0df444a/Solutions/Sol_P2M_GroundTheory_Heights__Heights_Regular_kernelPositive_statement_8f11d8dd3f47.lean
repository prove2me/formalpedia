-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_kernelPositive_statement_8f11d8dd3f47
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:57:03.610568+00:00
-- url     : https://prove2.me/submissions/36ed7899-abdc-4289-a1a6-600021e29757

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PKernelPositive
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_cquad_im_a0b693d24644
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_im_pos_of_punctured_925a660c5ab1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_pos_of_punctured_8ced2c649aa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_KernelPositive_line_apply_0ab5ddcbd25d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Matrix
noncomputable section
open KernelPositive
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution : KernelPositive.Statement := by
  intro n a g P T0 hT v hv hB z hz
  rw [← cquad_im]
  have hLa : AnalyticAt ℂ (line z) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hL0 : line z 0 = z := by simp [line]
  have hG : AnalyticAt ℂ (fun t => cquad v (T0 (line z t))) 0 := by
    have h : (fun t => cquad v (T0 (line z t))) =
        ∑ p, ∑ q, fun t => (v p : ℂ) * (T0 (line z t) p q * (v q : ℂ)) := by
      funext t
      simp [cquad, dotProduct, mulVec, Finset.sum_apply, Finset.mul_sum]
    rw [h]
    refine Finset.analyticAt_sum _ fun p _ => Finset.analyticAt_sum _ fun q _ => ?_
    exact analyticAt_const.mul
      ((AnalyticAt.comp_of_eq (hT.1 p q z hz) hLa hL0).mul analyticAt_const)
  have hball : ∀ᶠ t in 𝓝 (0 : ℂ), line z t ∈ ball (0 : Fin n → ℂ) 1 :=
    hLa.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (by rw [hL0]; exact hz))
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ k, line z t k ≠ 0 := by
    refine Filter.eventually_all.mpr fun k => ?_
    by_cases hzk : z k = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [line_apply, hzk, zero_add]
      exact ht
    · have hc : ContinuousAt (fun t : ℂ => z k + t) 0 :=
        (continuous_const.add continuous_id).continuousAt
      have := hc.eventually_ne (by simpa using hzk)
      exact nhdsWithin_le_nhds (this.mono fun t ht => by rw [line_apply]; exact ht)
  have hpos : ∀ᶠ t in 𝓝[≠] (0 : ℂ), 0 < (cquad v (T0 (line z t))).im := by
    filter_upwards [nhdsWithin_le_nhds hball, hne] with t ht1 ht2
    exact pos_of_punctured P hT hv hB ht1 ht2
  have := im_pos_of_punctured hG hpos
  simpa only [hL0] using this
end GroundTheory.Heights₂.Heights.Regular
