-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_Dominates_equiv_25ce9aaa0a49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:10:51.902228+00:00
-- url     : https://prove2.me/submissions/abb97562-5cce-4ed3-9f94-767f779f3493

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Imports

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace Dominates
theorem _root_.solution (A : Type*) {K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    [Algebra A K] (V : Subring K) :
    GroundTheory.Heights₂.Heights.Model.Dominates A V ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.Dominates A V :=
  Iff.rfl
end Dominates
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
