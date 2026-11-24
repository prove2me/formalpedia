-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_chartRing_onePoint_d03e9839999f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:34.25217+00:00
-- url     : https://prove2.me/submissions/84558f0e-dc8f-4f4e-8c66-3deb9a4f8cc6

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
theorem _root_.solution (o : Type) [CommRing o] [Algebra o ℚ] :
    chartRing o onePoint () = ⊥ := by
  have h : Set.range (fun j : Unit => onePoint j / onePoint ()) = {1} := by
    ext y
    simp [onePoint, eq_comm]
  rw [chartRing, h]
  exact Algebra.adjoin_singleton_one _ _
end GroundTheory.Heights₂.Heights.Model
