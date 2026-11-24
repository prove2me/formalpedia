-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_locRing_algebraMap_cone_coe_cb5a4a87300e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:35.505794+00:00
-- url     : https://prove2.me/submissions/2c6070e5-f3ec-4540-a090-73f6e4541da0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
namespace locRing
theorem _root_.solution (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W)
    (x : locRing P W) :
    ((algebraMap (locRing P W) (coneLocRing P W hPW) x : coneLocRing P W hPW) :
      FractionRing (MRing ι ⧸ P)) = x :=
  rfl
end locRing
end GroundTheory.Heights₂.Heights.Inter
