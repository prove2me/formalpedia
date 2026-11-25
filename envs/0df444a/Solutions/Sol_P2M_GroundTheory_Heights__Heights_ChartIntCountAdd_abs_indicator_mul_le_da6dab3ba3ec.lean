-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartIntCountAdd_abs_indicator_mul_le_da6dab3ba3ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:36:23.435205+00:00
-- url     : https://prove2.me/submissions/d2027db3-de1c-4764-8ba4-40070b86ed4e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartIntCountAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartIntCountAdd

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.ChartIntCountAdd
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartIntCountAdd
theorem _root_.solution (S : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℝ) (x : Fin n → ℂ) (c : ℝ) :
    |S.indicator f x * c| ≤ |f x * c| := by
  by_cases hx : x ∈ S <;> simp [hx] <;> positivity
end GroundTheory.Heights₂.Heights.ChartIntCountAdd
