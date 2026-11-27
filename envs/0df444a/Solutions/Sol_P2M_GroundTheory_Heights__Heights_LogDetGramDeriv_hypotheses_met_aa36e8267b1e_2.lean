-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_LogDetGramDeriv_hypotheses_met_aa36e8267b1e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:19.198094+00:00
-- url     : https://prove2.me/submissions/01ee8e44-3eb2-4db1-9a9a-36ba748dc648

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
namespace LogDetGramDeriv
theorem _root_.solution :
    (1 : ℝ) ≤ ((1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * ((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹).map
      (fun x : ℝ => (x : ℂ)) * (1 : Matrix (Fin 1) (Fin 1) ℂ)).det.re := by
  simp
end LogDetGramDeriv
end GroundTheory.Heights₂.Heights
