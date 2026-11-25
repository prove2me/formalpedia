-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_chartInv_chartInv_c2422d3ef73b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:28.688575+00:00
-- url     : https://prove2.me/submissions/e177177e-d89c-4340-8d84-7267e248964a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
open ChartMongeAmpereAffineInvariance
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
theorem _root_.solution {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : chartInv (chartInv y) = y := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp [chartInv]
  · simp only [chartInv, hj, if_false, if_true]
    field_simp
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
