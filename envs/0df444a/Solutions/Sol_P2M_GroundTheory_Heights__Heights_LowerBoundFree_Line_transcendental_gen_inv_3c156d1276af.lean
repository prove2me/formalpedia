-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_gen_inv_3c156d1276af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:03:35.141689+00:00
-- url     : https://prove2.me/submissions/f8de1a96-8457-4810-b5e9-087b14e00775

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_div_d53045909a4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_coe_gen_12d21276c6ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_of_coe_f7a530295392

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
theorem _root_.solution : Transcendental ℚ gen⁻¹ := by
  refine transcendental_of_coe ?_
  rw [IntermediateField.coe_inv, coe_gen, u, inv_div]
  exact transcendental_div (by decide)
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
