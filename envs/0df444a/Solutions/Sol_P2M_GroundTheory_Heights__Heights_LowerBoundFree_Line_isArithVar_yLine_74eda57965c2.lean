-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_isArithVar_yLine_74eda57965c2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:24.389098+00:00
-- url     : https://prove2.me/submissions/785e1230-a0f8-4462-b510-f0ae42c34e4b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mCoordIdeal_yLine_1445442fc678
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isArithVar_projLine_149b03129df9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution : IsArithVar (mCoordIdeal yLine) 2 := by
  rw [mCoordIdeal_yLine]
  exact Inter.isArithVar_projLine
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
