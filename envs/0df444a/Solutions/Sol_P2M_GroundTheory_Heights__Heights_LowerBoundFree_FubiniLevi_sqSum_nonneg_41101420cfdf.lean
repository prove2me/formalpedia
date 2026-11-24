-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_sqSum_nonneg_41101420cfdf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:23.573537+00:00
-- url     : https://prove2.me/submissions/f697260e-cc81-40cf-9669-eaab9f8c7dab

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
theorem _root_.solution (z : J → ℂ) : 0 ≤ sqSum z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
