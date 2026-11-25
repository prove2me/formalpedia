-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermLine_log_div_toGeo_h_fb686777305f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:05.538323+00:00
-- url     : https://prove2.me/submissions/2f25b55c-7761-4276-94bd-b39e1195cc3c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_IsSaturatedFirstCoordinateLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CurveIsOrbit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_MemMCoordIdealIffOfIsWeightedHomogeneous

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.HermLine
namespace GroundTheory.Heights₂.Heights.HermLine
theorem _root_.solution (A A' : HermLine n) {z : Cone n ℂ} (hz : BlockNonzero z) :
    Real.log (A.toGeo.h (flatCone z) / A'.toGeo.h (flatCone z)) =
      Real.log (A.metric z) - Real.log (A'.metric z) := by
  rw [toGeo_h_of_blockNonzero A (w := flatCone z) hz,
    toGeo_h_of_blockNonzero A' (w := flatCone z) hz]
  exact Real.log_div (A.metric_pos z hz).ne' (A'.metric_pos z hz).ne'
end GroundTheory.Heights₂.Heights.HermLine
