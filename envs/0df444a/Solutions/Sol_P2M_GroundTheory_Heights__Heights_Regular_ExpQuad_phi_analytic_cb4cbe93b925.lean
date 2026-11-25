-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_phi_analytic_cb4cbe93b925
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:56:54.298195+00:00
-- url     : https://prove2.me/submissions/d3ce91a4-b93c-4efd-aef2-0c616fe5aa97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_finsetSum_2318fa4c3e17
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_coord_div_mul_a8bafecb8e64
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_tau_shifted_entry_aa219638b1b6

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
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
variable {n a g : ℕ} (P : PeriodPolydisc n a g) (v : Fin g → ℤ)
namespace GroundTheory.Heights₂.Heights.Regular.ExpQuad
theorem _root_.solution : AnalyticOnNhd ℂ (phi P v) (logCover P.a_le) := by
  intro w hw
  have he : ∀ p q, AnalyticAt ℂ (fun x => P.tau0 x p q) w := by
    intro p q
    simp only [tau_shifted_entry]
    exact (P.analytic p q w hw).sub
      (analyticAt_finsetSum _ fun i _ => analyticAt_coord_div_mul _ _ _ w)
  have hq : AnalyticAt ℂ (fun x => qf (P.tau0 x) v) w := by
    simp only [qf, dotProduct, mulVec]
    refine analyticAt_finsetSum _ fun p _ => analyticAt_const.mul ?_
    exact analyticAt_finsetSum _ fun q _ => (he p q).mul analyticAt_const
  exact analyticAt_const.mul hq
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
