-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_VerticalDegreeAfterAdjoining_chart_congr_8f517aba47f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:43.384168+00:00
-- url     : https://prove2.me/submissions/ae9a7999-f8e6-4025-9b5e-05f0cff34614

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiProjPrimeImageZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankAdjoinFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFnDegAdjoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartScalingIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StAdjoinIndepRelfinrank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFinrankAdjoinRange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ChartCongr

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace VerticalDegreeAfterAdjoining
theorem _root_.solution {K' Ω : Type*} {ι' : K' → Type*} (x' : (Σ k', ι' k') → Ω)
    (i' : ∀ k', ι' k') {a b : K'} (h : a = b) : x' ⟨a, i' a⟩ = x' ⟨b, i' b⟩ := by
  subst h
  rfl
end VerticalDegreeAfterAdjoining
end GroundTheory.Heights₂.Heights.Inter
