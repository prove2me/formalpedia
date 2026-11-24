-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_chartLin_apply_d879f0c04e2e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:17.828459+00:00
-- url     : https://prove2.me/submissions/84042812-bc25-44dd-b396-8dfa13be7061

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartHessCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChartGramHess
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartHessCompare

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
theorem _root_.solution (y : Fin e → ℂ) :
    chartLin B y = WithLp.toLp 2 (B *ᵥ (Fin.cons 0 y : Fin (e + 1) → ℂ)) := rfl
end GroundTheory.Heights₂.Heights.ChartHessianComparison
