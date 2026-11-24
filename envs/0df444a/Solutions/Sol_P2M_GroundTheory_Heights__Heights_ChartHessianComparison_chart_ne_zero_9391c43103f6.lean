-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_ne_zero_9391c43103f6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:52.077261+00:00
-- url     : https://prove2.me/submissions/f39d1c57-1999-4767-b3b8-3d5de4263302

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_add_96698a2c7bee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_toLp_mulVec_ne_zero_ab75d852d29d

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder InnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.ChartHessianComparison
variable {e : ℕ} (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
namespace GroundTheory.Heights₂.Heights.ChartHessianComparison
theorem _root_.solution (hB : B.det ≠ 0) (y : Fin e → ℂ) : chartConst B + chartLin B y ≠ 0 := by
  rw [chart_add]
  refine toLp_mulVec_ne_zero B hB fun h => ?_
  have := congrFun h 0
  simp at this
end GroundTheory.Heights₂.Heights.ChartHessianComparison
