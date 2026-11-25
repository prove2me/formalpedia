-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_continuous_sqSum_68d304758819
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:03:46.957525+00:00
-- url     : https://prove2.me/submissions/9ef80a28-42e8-433d-91df-2f49e1c7ec1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
theorem _root_.solution : Continuous (sqSum : (J → ℂ) → ℝ) := by
  unfold sqSum
  fun_prop
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
