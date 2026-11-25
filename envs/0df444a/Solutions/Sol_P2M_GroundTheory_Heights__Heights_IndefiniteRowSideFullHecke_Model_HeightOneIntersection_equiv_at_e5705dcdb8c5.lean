-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_equiv_at_e5705dcdb8c5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:04.536259+00:00
-- url     : https://prove2.me/submissions/8f6b6ac9-9c8e-48a7-bb41-3a68eb26ed86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_EquivAt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_bot_183bb0b88058
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_HeightOneIntersection_coe_iInf_dc81a4ab244c

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
    (Subalgebra.toSubmodule (⊥ : Subalgebra A K) =
      ⨅ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
        GroundTheory.Heights₂.Heights.Model.localizedIn p.asIdeal
          (Subalgebra.toSubmodule (⊥ : Subalgebra A K))) ↔
      Set.range (algebraMap A K) =
        ⋂ (p : Ideal A) (_ : p.IsPrime) (_ : p.height = 1), locIn A K p := by
  rw [← HeightOneIntersection.coe_bot, ← HeightOneIntersection.coe_iInf]
  exact SetLike.coe_set_eq.symm
end HeightOneIntersection
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
