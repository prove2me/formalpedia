-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ChartScalingIndep_isHomogeneous_mw_6c8ae1086a4a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:13:39.45745+00:00
-- url     : https://prove2.me/submissions/589e4358-1c68-429e-a680-249ee36715a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CurvePt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartScalingIndep
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_mem_weighted_of_isMultiHomog


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep
theorem _root_.solution {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) :
    V.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hV
  refine Ideal.homogeneous_span _ S fun f hf => ?_
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, mem_weighted_of_isMultiHomog ha⟩
end GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep
