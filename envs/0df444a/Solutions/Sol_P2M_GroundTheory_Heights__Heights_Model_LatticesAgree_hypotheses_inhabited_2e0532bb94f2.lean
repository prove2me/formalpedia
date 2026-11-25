-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_LatticesAgree_hypotheses_inhabited_2e0532bb94f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:07.315728+00:00
-- url     : https://prove2.me/submissions/316e5024-4b85-4b44-aa87-a42325176f67

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
namespace LatticesAgree
theorem _root_.solution :
    Module.Finite ℤ (Submodule.span ℤ {(1 : ℚ)}) ∧
      Module.Projective ℤ (Submodule.span ℤ {(1 : ℚ)}) ∧
      Submodule.span ℚ ((Submodule.span ℤ {(1 : ℚ)} : Submodule ℤ ℚ) : Set ℚ) = ⊤ := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [eq_top_iff]
  intro v _
  have h1 : (1 : ℚ) ∈ Submodule.span ℚ ((Submodule.span ℤ {(1 : ℚ)} : Submodule ℤ ℚ) : Set ℚ) :=
    Submodule.subset_span (Submodule.subset_span rfl)
  have h2 := Submodule.smul_mem _ v h1
  rwa [smul_eq_mul, mul_one] at h2
end LatticesAgree
end GroundTheory.Heights₂.Heights.Model
