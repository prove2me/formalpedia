-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermLine_toGeo_ofGeo_h_01fd03adcfe5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:40.777731+00:00
-- url     : https://prove2.me/submissions/1a15d63d-f434-435d-b3b1-785108bbd31c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_TargetSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Reading

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
namespace HermLine
theorem _root_.solution (N : Geo.HermLine (blockIdx n)) (hN : Geo.IsSmoothHerm N)
    {w : Coord n → ℂ} (hw : BlockNonzero (unflatCone w)) : (HermLine.ofGeo N hN).toGeo.h w = N.h w :=
  HermLine.toGeo_h_of_blockNonzero _ hw
end HermLine
end GroundTheory.Heights₂.Heights
