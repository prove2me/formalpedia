-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_DiagonalPullback_pullDeg_eq_alt_cab5d464467e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:19.144824+00:00
-- url     : https://prove2.me/submissions/72ebf008-7148-4178-8ba0-ca47ec934009

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsDiagPull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PDiagPullI
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullDeg_otherLine_3e6f27535fdb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pullDeg_segreBlockEmbedding_ebc096d97a8e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 DiagRAux
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
namespace GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
theorem _root_.solution (j : Fin 2) (c : T.YBlk → ℤ) : I1.pullDeg (diagonalBlockIndex j) c = T.pullDeg j c := by
  funext k
  fin_cases j <;> cases k
  · exact pullDeg_segreBlockEmbedding 0 c .base
  · exact pullDeg_segreBlockEmbedding 0 c .det
  · exact pullDeg_segreBlockEmbedding 0 c .line
  · exact pullDeg_otherLine 0 c
  · exact pullDeg_segreBlockEmbedding 1 c .base
  · exact pullDeg_segreBlockEmbedding 1 c .det
  · exact pullDeg_otherLine 1 c
  · exact pullDeg_segreBlockEmbedding 1 c .line
end GroundTheory.Heights₂.Heights.Inter.DiagonalPullback
