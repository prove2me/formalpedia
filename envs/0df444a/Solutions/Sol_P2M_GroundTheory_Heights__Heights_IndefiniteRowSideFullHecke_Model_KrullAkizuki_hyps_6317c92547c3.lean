-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_KrullAkizuki_hyps_6317c92547c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:00:17.103572+00:00
-- url     : https://prove2.me/submissions/d3f67078-ea44-4587-8609-3531eac6bb96

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
namespace KrullAkizuki
theorem _root_.solution :
    IsNoetherianRing ℤ ∧ IsFractionRing ℤ ℚ ∧ FiniteDimensional ℚ ℚ ∧ IsScalarTower ℤ ℚ ℚ ∧
      ringKrullDim ℤ = 1 :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField⟩
end KrullAkizuki
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
