-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FiniteIntegralClosure_hypotheses_inhabited_1deaa4585a79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:25:13.95185+00:00
-- url     : https://prove2.me/submissions/6cef619a-e551-4dd5-b81b-5ded194b8c3f

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
namespace FiniteIntegralClosure
theorem _root_.solution :
    IsDomain ℤ ∧ Algebra.FiniteType ℤ ℤ ∧ IsFractionRing ℤ ℚ ∧
      FiniteDimensional ℚ (CyclotomicField 3 ℚ) ∧ IsScalarTower ℤ ℚ (CyclotomicField 3 ℚ) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
end FiniteIntegralClosure
end GroundTheory.Heights₂.Heights.Model
