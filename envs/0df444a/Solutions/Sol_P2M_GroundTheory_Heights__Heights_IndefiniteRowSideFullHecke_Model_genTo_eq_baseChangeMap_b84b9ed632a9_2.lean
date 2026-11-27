-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_eq_baseChangeMap_b84b9ed632a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:59:48.654848+00:00
-- url     : https://prove2.me/submissions/a7c85702-ff1a-422b-8e4c-a9f402cc80a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsVectorBundleIffModel

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
open CategoryTheory Opposite AlgebraicGeometry Limits
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution (X : Scheme.{0}) :
    genTo X = GroundTheory.Heights₂.Heights.Model.baseChangeMap (toSpecZ X) ℚ := rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
