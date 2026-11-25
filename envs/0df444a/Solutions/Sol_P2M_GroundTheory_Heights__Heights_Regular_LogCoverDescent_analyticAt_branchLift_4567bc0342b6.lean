-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_branchLift_4567bc0342b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:18.610918+00:00
-- url     : https://prove2.me/submissions/319cef3e-47a3-4f98-a8be-fefd469679e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_eval_27b94d595884

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
open Metric Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
variable {n a : ℕ} (h : a ≤ n)
variable {h}
omit h
namespace GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
theorem _root_.solution {z0 : Fin n → ℂ} (h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0) :
    AnalyticAt ℂ (branchLift a z0) z0 := by
  refine AnalyticAt.pi (f := fun k z => branchLift a z0 z k) fun k => ?_
  by_cases hk : k.val < a
  · simp only [branchLift, if_pos hk]
    refine AnalyticAt.add (AnalyticAt.clog ?_ ?_) analyticAt_const
    · exact (analyticAt_eval k z0).div analyticAt_const (h0 k hk)
    · rw [div_self (h0 k hk)]
      exact Complex.one_mem_slitPlane
  · simp only [branchLift, if_neg hk]
    exact analyticAt_eval k z0
end GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
