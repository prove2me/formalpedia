-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_det_one_add_comp_6312c74855cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:54:25.318146+00:00
-- url     : https://prove2.me/submissions/ac91eebf-7d8f-45a1-821c-629c1bc8a0e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaMultiplicity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphAreaHolomorphic
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphAreaHolomorphic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Module
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
namespace GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
theorem _root_.solution {E E' H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (φ : E ≃ₗᵢ[ℝ] E') (L : E' →ₗ[ℝ] H) :
    LinearMap.det (1 + LinearMap.adjoint (L ∘ₗ φ.toLinearMap) ∘ₗ (L ∘ₗ φ.toLinearMap)) =
      LinearMap.det (1 + LinearMap.adjoint L ∘ₗ L) := by
  rw [← LinearMap.det_conj (1 + LinearMap.adjoint L ∘ₗ L) φ.symm.toLinearEquiv]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
end GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
