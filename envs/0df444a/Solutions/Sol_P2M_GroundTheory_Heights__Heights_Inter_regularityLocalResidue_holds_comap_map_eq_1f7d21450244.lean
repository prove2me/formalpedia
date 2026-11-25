-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalResidue_holds_comap_map_eq_1f7d21450244
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:59:05.321587+00:00
-- url     : https://prove2.me/submissions/78e7aaa7-bd44-434b-b1eb-33b3a1502dd4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsTerRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsUnitOfNumMem

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
open GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hI : RingHom.ker f ≤ I) : (I.map f).comap f = I := by
  rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hI]
end GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds
