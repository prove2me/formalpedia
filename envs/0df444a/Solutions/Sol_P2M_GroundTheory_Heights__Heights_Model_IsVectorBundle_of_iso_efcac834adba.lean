-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_IsVectorBundle_of_iso_efcac834adba
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:38.905802+00:00
-- url     : https://prove2.me/submissions/cf019a06-1831-4983-a509-d5bf9347f15d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_IsBasisOn_of_iso_15fe1f0a6e57

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
universe u
variable {X Y : Scheme.{u}}
namespace GroundTheory.Heights₂.Heights.Model
namespace IsVectorBundle
theorem _root_.solution {M N : X.Modules} (e : M ≅ N) (hM : IsVectorBundle M) :
    IsVectorBundle N := by
  intro x
  obtain ⟨U, hU, hx, n, s, hs⟩ := hM x
  exact ⟨U, hU, hx, n, _, hs.of_iso e⟩
end IsVectorBundle
end GroundTheory.Heights₂.Heights.Model
