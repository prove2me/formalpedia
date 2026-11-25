-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_sub_to_fa96747bb723
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:20:26.495856+00:00
-- url     : https://prove2.me/submissions/437c03b2-3bfe-475a-bb18-6a5ba2e9c09f

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
    ∃ w : (subOpen X a m').toScheme ⟶ (invOpen X (a * m')).toScheme,
      w ≫ X.homOfLE (invOpen_le X a m') = (subOpen X a m').ι := by
  refine ⟨IsOpenImmersion.lift (invOpen X (a * m')).ι ((subOpen X a m').ι ≫ (invOpen X a).ι) ?_, ?_⟩
  · rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    have hs : (subOpen X a m').ι.base s ∈ subOpen X a m' :=
      (Scheme.Opens.range_ι (subOpen X a m')).subset ⟨s, rfl⟩
    exact hs
  · rw [← cancel_mono (invOpen X a).ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
