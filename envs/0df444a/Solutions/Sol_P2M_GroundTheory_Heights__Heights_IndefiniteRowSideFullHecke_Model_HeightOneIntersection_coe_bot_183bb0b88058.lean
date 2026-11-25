-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_bot_183bb0b88058
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:33:18.959361+00:00
-- url     : https://prove2.me/submissions/a7d577db-dc23-448b-81ac-3677eed13710

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_EquivAt

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
variable (A K : Type) [CommRing A] [Field K] [Algebra A K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace HeightOneIntersection
theorem _root_.solution :
    ((Subalgebra.toSubmodule (⊥ : Subalgebra A K) : Submodule A K) : Set K) =
      Set.range (algebraMap A K) := by
  ext x
  exact Algebra.mem_bot
end HeightOneIntersection
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
