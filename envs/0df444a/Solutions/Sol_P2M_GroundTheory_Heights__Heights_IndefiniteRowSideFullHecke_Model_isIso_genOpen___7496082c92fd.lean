-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_genOpen___7496082c92fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:34.062956+00:00
-- url     : https://prove2.me/submissions/eabcf7f7-023b-44fb-b047-683f02b93796

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genTo_mem_invOpen_6f185c6bdade

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
open CategoryTheory AlgebraicGeometry
variable (X : Scheme.{0})
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution {a : ℕ} (ha : 0 < a) : IsIso (genOpen X a).ι :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
    rw [Scheme.Opens.opensRange_ι]
    exact top_unique fun x _ => genTo_mem_invOpen X ha.ne' x)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
