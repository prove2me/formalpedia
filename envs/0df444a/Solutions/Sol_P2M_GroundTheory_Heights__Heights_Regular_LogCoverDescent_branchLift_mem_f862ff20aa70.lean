-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_branchLift_mem_f862ff20aa70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:21.306208+00:00
-- url     : https://prove2.me/submissions/a1bb8dbe-d2d9-4ac2-9ae8-2df2e94c3e94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PLogCoverDescent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_ne_zero_of_mem_a8cb1672c599
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_norm_lt_one_of_mem_cfee7e062e03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_LogCoverDescent_exp_branchLift_6efc6e3b6b62

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
namespace GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
theorem _root_.solution {z0 z : Fin n → ℂ} (h0 : z0 ∈ puncturedChart h (ball 0 1))
    (hz : z ∈ puncturedChart h (ball 0 1)) : branchLift a z0 z ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.2
    have e := exp_branchLift hi (ne_zero_of_mem h0 _ hi) (ne_zero_of_mem hz _ hi)
    have hn := norm_lt_one_of_mem hz (Fin.castLE h i)
    rw [← e, Complex.norm_exp] at hn
    exact Real.exp_lt_one_iff.1 hn
  · simp only [branchLift, if_neg (by omega : ¬ k.val < a)]
    exact norm_lt_one_of_mem hz k
end GroundTheory.Heights₂.Heights.Regular.LogCoverDescent
