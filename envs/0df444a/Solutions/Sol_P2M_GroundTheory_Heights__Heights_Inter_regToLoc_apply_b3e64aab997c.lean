-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regToLoc_apply_b3e64aab997c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:03:44.695689+00:00
-- url     : https://prove2.me/submissions/87187caf-d7bf-44d7-b666-25cc47541aa6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingInj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IntCastMemRegMaxAt

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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {P W : Ideal (MRing ι)} (hW : IsClosedPt W) (hPW : P ≤ W) (x : regRing P) :
    regToLoc P W hW hPW x = ⟨((x : funField P) : FractionRing (MRing ι ⧸ P)), regRing_mem_locRing hW hPW x⟩ :=
  rfl
end GroundTheory.Heights₂.Heights.Inter
