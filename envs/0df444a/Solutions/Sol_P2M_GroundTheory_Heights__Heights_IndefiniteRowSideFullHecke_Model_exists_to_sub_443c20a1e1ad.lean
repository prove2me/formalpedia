-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_to_sub_443c20a1e1ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:07:25.971701+00:00
-- url     : https://prove2.me/submissions/ff28ea5c-3732-48f7-810f-ce996ffd6c20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff

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
theorem _root_.solution (a m' : ℕ) :
    ∃ w' : (invOpen X (a * m')).toScheme ⟶ (subOpen X a m').toScheme,
      w' ≫ (subOpen X a m').ι = X.homOfLE (invOpen_le X a m') := by
  refine ⟨IsOpenImmersion.lift (subOpen X a m').ι (X.homOfLE (invOpen_le X a m')) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  show ((X.homOfLE (invOpen_le X a m') ≫ (invOpen X a).ι)).base y ∈ invOpen X (a * m')
  rw [Scheme.homOfLE_ι]
  exact (Scheme.Opens.range_ι _).subset ⟨y, rfl⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
