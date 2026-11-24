-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartHessianComparison_toLp_mulVec_ne_zero_ab75d852d29d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:57.185806+00:00
-- url     : https://prove2.me/submissions/4a5940ef-8f12-4a43-9cf2-f485f4b24875

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
theorem _root_.solution (hB : B.det ≠ 0) {v : Fin (e + 1) → ℂ} (hv : v ≠ 0) :
    (WithLp.toLp 2 (B *ᵥ v) : EuclideanSpace ℂ (Fin (e + 1))) ≠ 0 := by
  intro h
  apply hv
  apply eq_zero_of_mulVec_eq_zero hB
  have := congrArg WithLp.ofLp h
  simpa using this
end GroundTheory.Heights₂.Heights.ChartHessianComparison
