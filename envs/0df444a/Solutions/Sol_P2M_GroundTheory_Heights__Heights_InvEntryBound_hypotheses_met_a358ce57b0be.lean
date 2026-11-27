-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_InvEntryBound_hypotheses_met_a358ce57b0be
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:02:33.554814+00:00
-- url     : https://prove2.me/submissions/e06bbc8f-288c-4d8d-9cfb-a1e096c7eb6c

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
namespace InvEntryBound
theorem _root_.solution :
    (1 : Matrix (Fin 2) (Fin 2) ℝ) - (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 ∧
      (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef :=
  ⟨by simp, PosSemidef.zero⟩
end InvEntryBound
end GroundTheory.Heights₂.Heights
