-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_KrullAkizuki_hypotheses_inhabited_dfb5af3f6c1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:01.590644+00:00
-- url     : https://prove2.me/submissions/243b99aa-a4ff-457c-893f-b99f4badff24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
namespace KrullAkizuki
theorem _root_.solution :
    IsNoetherianRing ℤ ∧ ringKrullDim ℤ = 1 ∧ IsFractionRing ℤ ℚ ∧ FiniteDimensional ℚ ℚ ∧
      IsScalarTower ℤ ℚ ℚ :=
  ⟨inferInstance, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField, inferInstance,
    inferInstance, inferInstance⟩
end KrullAkizuki
end GroundTheory.Heights₂.Heights.Model
