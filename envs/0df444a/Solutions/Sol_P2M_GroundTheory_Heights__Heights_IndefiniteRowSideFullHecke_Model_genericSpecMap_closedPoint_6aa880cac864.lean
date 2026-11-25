-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericSpecMap_closedPoint_6aa880cac864
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:39.501047+00:00
-- url     : https://prove2.me/submissions/4241c2d3-20c7-46b0-babc-3bfa3109f635

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_FiniteTypeSectionsOfIsFiniteTypeOverZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution (Z : Scheme.{0}) [IsIntegral Z] (L : Type) [Field L]
    [Algebra Z.functionField L] :
    _root_.GroundTheory.Heights₂.Heights.Model.genericSpecMap Z L (IsLocalRing.closedPoint L) =
      genericPoint Z := by
  have h : (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
      (IsLocalRing.closedPoint (CommRingCat.of L)) = IsLocalRing.closedPoint Z.functionField :=
    Spec_closedPoint
  exact (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)))
    (Z.fromSpecStalk (genericPoint Z)) (IsLocalRing.closedPoint (CommRingCat.of L))).trans
    (h ▸ Scheme.fromSpecStalk_closedPoint)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
