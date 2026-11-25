-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_genFib_to_fc6efea8f4ed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:06:51.53847+00:00
-- url     : https://prove2.me/submissions/bf762a8b-46bb-4d35-b05b-2242290df8a4

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
theorem _root_.solution {m : ℕ} (hm : m ≠ 0) :
    ∃ t : genFib X ⟶ (invOpen X m).toScheme, t ≫ (invOpen X m).ι = genTo X :=
  ⟨IsOpenImmersion.lift _ _ (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact genTo_mem_invOpen X hm x), IsOpenImmersion.lift_fac _ _ _⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
