-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_BlowUpChart_hypotheses_inhabited_04be7bb79312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:47.733185+00:00
-- url     : https://prove2.me/submissions/4c8deca3-a6a0-49ce-bb7d-af5e19a234d9

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
namespace BlowUpChart
theorem _root_.solution :
    Ideal.span (Set.range ![(2 : ℤ_[2])]) = IsLocalRing.maximalIdeal ℤ_[2] ∧
      ∃ j, ![(2 : ℤ_[2])] j ≠ 0 := by
  refine ⟨?_, ⟨0, by simp⟩⟩
  rw [PadicInt.maximalIdeal_eq_span_p]
  simp
end BlowUpChart
end GroundTheory.Heights₂.Heights.Model
