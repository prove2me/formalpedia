-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GraphAreaHolomorphic_adjoint_comp_self_of_norm_406da87f1cbf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:19.874021+00:00
-- url     : https://prove2.me/submissions/caa50a27-5c47-4b30-9441-3ded84d6c2a4

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
theorem _root_.solution {E H K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    (T : E →ₗ[ℝ] K) (L : E →ₗ[ℝ] H) (h : ∀ v, ‖T v‖ ^ 2 = ‖v‖ ^ 2 + ‖L v‖ ^ 2) :
    LinearMap.adjoint T ∘ₗ T = 1 + LinearMap.adjoint L ∘ₗ L := by
  refine LinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Module.End.one_apply, inner_add_left,
    LinearMap.adjoint_inner_left]
  simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add]
  have h1 := h (v + w)
  have h2 := h v
  have h3 := h w
  simp only [sq] at h1 h2 h3
  linarith
end GroundTheory.Heights₂.Heights.GraphAreaHolomorphic
