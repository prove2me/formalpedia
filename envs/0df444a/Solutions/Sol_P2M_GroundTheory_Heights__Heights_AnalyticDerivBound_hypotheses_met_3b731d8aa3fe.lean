-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AnalyticDerivBound_hypotheses_met_3b731d8aa3fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:35.051315+00:00
-- url     : https://prove2.me/submissions/857eac29-2461-4060-a4fc-ccacdfe2aad1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds

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
open Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace AnalyticDerivBound
theorem _root_.solution :
    IsOpen (Set.univ : Set ℂ) ∧ AnalyticOnNhd ℂ (fun x : ℂ => x) Set.univ ∧
      IsCompact (Metric.closedBall (0 : ℂ) 1) ∧ Metric.closedBall (0 : ℂ) 1 ⊆ Set.univ :=
  ⟨isOpen_univ, analyticOnNhd_id, isCompact_closedBall _ _, Set.subset_univ _⟩
end AnalyticDerivBound
end GroundTheory.Heights₂.Heights
