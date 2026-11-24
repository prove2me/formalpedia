-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_hermChartPot_eq_b52d42d77135
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:55.989221+00:00
-- url     : https://prove2.me/submissions/7c041cb7-e327-4dfc-a3b0-1efca7b96662

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_add_96698a2c7bee
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_inner_toLp_mulVec_9b675c86fb20

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
theorem _root_.solution :
    hermChartPot (Bᴴ * B) = fun y => 2⁻¹ * Real.log (⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ).re := by
  funext y
  unfold hermChartPot
  rw [← inner_toLp_mulVec, ← chart_add, Real.log_sqrt (show (0 : ℝ) ≤
    (⟪chartConst B + chartLin B y, chartConst B + chartLin B y⟫_ℂ).re from inner_self_nonneg (𝕜 := ℂ))]
  ring
end GroundTheory.Heights₂.Heights.ChartHessianComparison
