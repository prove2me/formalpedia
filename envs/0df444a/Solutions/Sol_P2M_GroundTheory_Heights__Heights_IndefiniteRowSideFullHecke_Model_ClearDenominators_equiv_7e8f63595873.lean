-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_ClearDenominators_equiv_7e8f63595873
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:59:27.109789+00:00
-- url     : https://prove2.me/submissions/de00c3dc-6929-4ecb-9532-e5712ba3fe92

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
namespace ClearDenominators
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.Model.ClearDenominators.Statement ↔ ClearDenominators.Statement := by
  constructor
  · intro h X _ _ hf L hL s
    exact h X (toSpecZ X) L hL s
  · intro h X f _ _ _ L hL s
    obtain rfl : f = toSpecZ X := specZ_hom_ext _ _
    exact h X inferInstance L hL s
end ClearDenominators
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
