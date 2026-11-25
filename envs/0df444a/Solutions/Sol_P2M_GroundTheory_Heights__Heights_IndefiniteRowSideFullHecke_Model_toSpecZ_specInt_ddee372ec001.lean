-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_toSpecZ_specInt_ddee372ec001
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:40.654821+00:00
-- url     : https://prove2.me/submissions/d6d32631-16da-4974-9c25-bf58f068612d

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit

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
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution : toSpecZ specInt = 𝟙 _ := specZ_hom_ext _ _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
