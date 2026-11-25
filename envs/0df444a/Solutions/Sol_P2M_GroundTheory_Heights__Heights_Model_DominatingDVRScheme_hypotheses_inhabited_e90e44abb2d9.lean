-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DominatingDVRScheme_hypotheses_inhabited_e90e44abb2d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:25:10.405551+00:00
-- url     : https://prove2.me/submissions/5715cb00-57cf-4e5c-b701-91e2db30ce72

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
namespace DominatingDVRScheme
theorem _root_.solution :
    IsIntegral SpecZ ∧ IsLocallyNoetherian SpecZ ∧ ∃ z : SpecZ, z ≠ genericPoint SpecZ := by
  refine ⟨inferInstance, inferInstance, ⟨⟨Ideal.span {(2 : ℤ)}, isPrime_span_prime ⟨2, Nat.prime_two⟩⟩, ?_⟩⟩
  rw [genericPoint_eq_bot_of_affine]
  intro h
  have := congrArg PrimeSpectrum.asIdeal h
  simp only [PrimeSpectrum.asIdeal_bot, Ideal.span_singleton_eq_bot] at this
  norm_num at this
end DominatingDVRScheme
end GroundTheory.Heights₂.Heights.Model
