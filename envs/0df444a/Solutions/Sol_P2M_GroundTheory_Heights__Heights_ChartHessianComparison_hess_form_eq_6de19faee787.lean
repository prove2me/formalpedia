-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hess_form_eq_6de19faee787
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:07:42.63658+00:00
-- url     : https://prove2.me/submissions/2840100f-fd13-40e9-a7bc-6fad75d317e8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_cxHessian_affine_form_a338950a1344
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hermChartPot_eq_b52d42d77135
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
theorem _root_.solution (hB : B.det ≠ 0) (y x : Fin e → ℂ) :
    star x ⬝ᵥ (cxHessian (hermChartPot (Bᴴ * B)) y *ᵥ x) = (hessForm B y x : ℂ) := by
  rw [hermChartPot_eq, cxHessian_affine_form _ _ _ _ (chart_ne_zero B hB y)]
  rfl
end GroundTheory.Heights₂.Heights.ChartHessianComparison
