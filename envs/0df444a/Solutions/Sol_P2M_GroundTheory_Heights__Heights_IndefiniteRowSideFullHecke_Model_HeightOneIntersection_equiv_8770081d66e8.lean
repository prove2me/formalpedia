-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_equiv_8770081d66e8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:00:01.75462+00:00
-- url     : https://prove2.me/submissions/d5d44aad-afc0-4f0d-8508-9daa927e0241

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_EquivAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_equiv_at_e5705dcdb8c5

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
namespace HeightOneIntersection
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.Statement ↔
      HeightOneIntersection.Statement := by
  constructor
  · intro h A K _ _ _ _ _ _ _
    exact (HeightOneIntersection.equiv_at A K).mp (h A K)
  · intro h A _ _ _ _ K _ _ _
    exact (HeightOneIntersection.equiv_at A K).mpr (h A K)
end HeightOneIntersection
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
