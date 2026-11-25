-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_geoNum_zero_nonneg_bca26a562c32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:45.465473+00:00
-- url     : https://prove2.me/submissions/7be55da5-efe4-4df4-85ae-d2f1d47a2a97

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_CardLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SpanSingletonEqRangeLsmul

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (b : Fin 0 → K → ℤ) : 0 ≤ geoNum 0 W b := by
  unfold geoNum
  split_ifs <;> positivity
end GroundTheory.Heights₂.Heights.Inter
