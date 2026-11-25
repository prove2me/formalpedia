-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_isMultiHomog_X_zero_b47684ca621c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:34.745228+00:00
-- url     : https://prove2.me/submissions/d12a0af6-5aac-4778-8492-0003fa9be56b

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
theorem _root_.solution :
    IsMultiHomog (MvPolynomial.X ⟨(), 0⟩ : MRing (fun _ : Unit => Fin 2) ℚ) (fun _ => 1) := by
  have := MvPolynomial.isWeightedHomogeneous_X ℚ (blockWeight (fun _ : Unit => Fin 2)) ⟨(), 0⟩
  have h : blockWeight (fun _ : Unit => Fin 2) ⟨(), 0⟩ = fun _ => 1 := by
    funext k
    simp [blockWeight]
  unfold IsMultiHomog
  rw [← h]
  exact this
end GroundTheory.Heights₂.Heights.Model
