-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_SumCp_hypotheses_inhabited_4ffa720a0d9f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:10.739463+00:00
-- url     : https://prove2.me/submissions/76ee3b5a-85c1-4d8c-a2e7-3b53f1b103f5

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
namespace SumCp
theorem _root_.solution :
    (6 : ℤ) ≠ 0 ∧ (2 : ℝ) ≤ 2 ∧
      ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime ∧ ((p : ℝ) ≤ 2 ∨ (p : ℤ) ∣ 6) := by
  refine ⟨by norm_num, le_rfl, ?_⟩
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · exact ⟨Nat.prime_two, Or.inl (by norm_num)⟩
  · rw [Finset.mem_singleton.mp hp]
    exact ⟨Nat.prime_three, Or.inr (by norm_num)⟩
end SumCp
end GroundTheory.Heights₂.Heights.Model
