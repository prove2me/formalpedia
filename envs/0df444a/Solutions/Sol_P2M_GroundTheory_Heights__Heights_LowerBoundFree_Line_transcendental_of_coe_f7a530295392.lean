-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_of_coe_f7a530295392
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:25.028825+00:00
-- url     : https://prove2.me/submissions/daf75c8e-d769-4440-8fed-57f1275460a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField

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
theorem _root_.solution {a : Ω} (ha : Transcendental ℚ (a : L)) : Transcendental ℚ a := by
  rw [transcendental_iff_injective, injective_iff_map_eq_zero] at ha ⊢
  intro p hp
  apply ha p
  have := congrArg (IntermediateField.val _) hp
  rw [map_zero, ← Polynomial.aeval_algHom_apply] at this
  exact this
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
