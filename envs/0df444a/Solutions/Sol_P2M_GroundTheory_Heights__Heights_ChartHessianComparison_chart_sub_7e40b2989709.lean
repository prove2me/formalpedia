-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_sub_7e40b2989709
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:11.561323+00:00
-- url     : https://prove2.me/submissions/b79c33bf-d2ab-4ae8-8261-3cdf6857b9d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chartLin_apply_d879f0c04e2e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chart_add_96698a2c7bee

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
theorem _root_.solution (y z : Fin e → ℂ) (t : ℂ) :
    chartLin B z - t • (chartConst B + chartLin B y) =
      WithLp.toLp 2 (B *ᵥ ((Fin.cons 0 z : Fin (e + 1) → ℂ) - t • Fin.cons 1 y)) := by
  rw [chart_add, chartLin_apply, mulVec_sub, mulVec_smul, WithLp.toLp_sub, WithLp.toLp_smul]
end GroundTheory.Heights₂.Heights.ChartHessianComparison
