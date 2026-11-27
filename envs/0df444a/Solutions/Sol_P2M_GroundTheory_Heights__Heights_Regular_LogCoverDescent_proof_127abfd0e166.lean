-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_proof_127abfd0e166
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:39.514863+00:00
-- url     : https://prove2.me/submissions/dbcc4b0d-3553-4f6a-9a22-dc190bc75c17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_eq_of_exp_eq_d620f9f7ef1f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_ne_zero_of_mem_a8cb1672c599
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_exp_branchLift_6efc6e3b6b62
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_branchLift_mem_f862ff20aa70
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_analyticAt_branchLift_4567bc0342b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_isOpen_puncturedChart_cd0b4adc3a14

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
open LogCoverDescent
namespace GroundTheory.Heights₂.Heights.Regular
namespace LogCoverDescent
theorem _root_.solution : LogCoverDescent.Statement := by
  intro n a h φ hφa hφ
  refine ⟨fun z0 hz0 => ?_, fun w hw => ?_⟩
  · have h0 : ∀ k : Fin n, k.val < a → z0 k ≠ 0 := ne_zero_of_mem hz0
    have hc : AnalyticAt ℂ (fun z => φ (branchLift a z0 z)) z0 :=
      (hφa _ (branchLift_mem hz0 hz0)).comp (analyticAt_branchLift h0)
    refine hc.congr ?_
    filter_upwards [(isOpen_puncturedChart (h := h)).mem_nhds hz0] with z hz
    symm
    refine eq_of_exp_eq hφ (branchLift_mem hz0 hz) fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · rw [exp_branchLift hk (h0 k hk) (ne_zero_of_mem hz k hk)]
      simp only [logLift, if_pos hk]
      exact Complex.exp_log (ne_zero_of_mem hz k hk)
    · simp only [logLift, branchLift, if_neg (by omega : ¬ k.val < a)]
  · refine eq_of_exp_eq hφ hw fun k => ⟨fun hk => ?_, fun hk => ?_⟩
    · simp only [logLift, expCover, if_pos hk]
      exact Complex.exp_log (Complex.exp_ne_zero _)
    · simp only [logLift, expCover, if_neg (by omega : ¬ k.val < a)]
end LogCoverDescent
end GroundTheory.Heights₂.Heights.Regular
