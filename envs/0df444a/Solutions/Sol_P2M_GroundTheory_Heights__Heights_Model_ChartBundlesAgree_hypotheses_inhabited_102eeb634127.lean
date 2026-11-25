-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_ChartBundlesAgree_hypotheses_inhabited_102eeb634127
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:36.991171+00:00
-- url     : https://prove2.me/submissions/04678d37-4a47-4829-8226-e166fbfbef0c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_normal_d96a8b1ad28c

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
namespace ChartBundlesAgree
theorem _root_.solution :
    IsNoetherianRing (chartRing ℤ onePoint ()) ∧ IsIntegrallyClosed (chartRing ℤ onePoint ()) ∧
      ∀ v ∈ (scaledTrivBundle ℤ onePoint 1 (one_ne_zero (α := ℚ))).lat (),
        ∃ s : chartRing ℤ onePoint (), s ≠ 0 ∧
          (s : ℚ) • v ∈ (scaledTrivBundle ℤ onePoint 1 (one_ne_zero (α := ℚ))).lat () :=
  ⟨chartRing_onePoint_normal.1, chartRing_onePoint_normal.2,
    fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
end ChartBundlesAgree
end GroundTheory.Heights₂.Heights.Model
