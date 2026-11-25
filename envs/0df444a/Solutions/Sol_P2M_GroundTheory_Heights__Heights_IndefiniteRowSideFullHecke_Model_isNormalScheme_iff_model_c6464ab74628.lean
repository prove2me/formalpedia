-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isNormalScheme_iff_model_c6464ab74628
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:05.365041+00:00
-- url     : https://prove2.me/submissions/a4a731a3-df7b-4303-953f-465461ae78c1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GenericImageEqGermImage

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
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
variable {X : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution (X : Scheme.{u}) [IsIntegral X] :
    GroundTheory.Heights₂.Heights.Model.IsNormalScheme X ↔ GroundTheory.Arith.SchemeCoh.IsNormalScheme X :=
  ⟨fun h => ⟨fun _ => inferInstance, h⟩, fun h => h.isIntegrallyClosed_stalk⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
