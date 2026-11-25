-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_coe_algebraMap_cone_190c0cf09fd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:26.045413+00:00
-- url     : https://prove2.me/submissions/07fd1d69-b20f-495d-9fa6-b5a5f15c44a7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap

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
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution (hPW : P ≤ W) (a : MRing ι ⧸ P) :
    ((algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) a : coneLocRing P W hPW) : FractionRing (MRing ι ⧸ P)) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) a :=
  rfl
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
