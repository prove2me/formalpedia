-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_gen_ne_zero_c3a5b642e033
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:23.577664+00:00
-- url     : https://prove2.me/submissions/26df70bf-1c98-4f81-8e74-5076e7429d71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_xL_ne_zero_6abe86b3f4b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_coe_gen_12d21276c6ec

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
theorem _root_.solution : gen ≠ 0 := by
  intro h
  have : (gen : L) = 0 := by rw [h]; rfl
  rw [coe_gen, u] at this
  exact div_ne_zero (xL_ne_zero 1) (xL_ne_zero 0) this
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
