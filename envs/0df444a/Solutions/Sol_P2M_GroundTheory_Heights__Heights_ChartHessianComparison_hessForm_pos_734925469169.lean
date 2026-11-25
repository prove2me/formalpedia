-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hessForm_pos_734925469169
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:42.209723+00:00
-- url     : https://prove2.me/submissions/bd2412a4-9ba2-4a0d-a1f9-76f90c8bb81c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_sub_7e40b2989709
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_toLp_mulVec_ne_zero_ab75d852d29d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_ne_zero_9391c43103f6

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
theorem _root_.solution (hB : B.det ≠ 0) (y : Fin e → ℂ) {x : Fin e → ℂ} (hx : x ≠ 0) :
    0 < hessForm B y x := by
  have hu := chart_ne_zero B hB y
  unfold hessForm
  rw [chart_sub]
  refine div_pos (pow_pos (norm_pos_iff.mpr (toLp_mulVec_ne_zero B hB fun h => hx ?_)) 2)
    (by have := norm_pos_iff.mpr hu; positivity)
  set t := ⟪chartConst B + chartLin B y, chartLin B (star x)⟫_ℂ /
      ⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ
  have h0 : t = 0 := by simpa using congrFun h 0
  funext k
  have hk := congrFun h k.succ
  simp [h0] at hk
  simpa using hk
end GroundTheory.Heights₂.Heights.ChartHessianComparison
