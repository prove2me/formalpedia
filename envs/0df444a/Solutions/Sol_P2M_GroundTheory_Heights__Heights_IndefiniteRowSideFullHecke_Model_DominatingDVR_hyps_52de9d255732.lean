-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_DominatingDVR_hyps_52de9d255732
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:59:45.796211+00:00
-- url     : https://prove2.me/submissions/1598b53d-921d-472a-9fde-1509357010da

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_closedPt_two_ne_generic_996421b7861e

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
namespace DominatingDVR
theorem _root_.solution :
    (IsDomain ℤ_[2] ∧ IsLocalRing ℤ_[2] ∧ IsNoetherianRing ℤ_[2] ∧ IsFractionRing ℤ_[2] ℚ_[2] ∧
      ¬ IsField ℤ_[2]) ∧
    (IsIntegral specInt ∧ IsLocallyNoetherian specInt ∧ closedPt prime2 ≠ genericPoint specInt) :=
  ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance,
    IsDiscreteValuationRing.not_isField ℤ_[2]⟩,
    ⟨inferInstance, inferInstance, closedPt_two_ne_generic⟩⟩
end DominatingDVR
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
