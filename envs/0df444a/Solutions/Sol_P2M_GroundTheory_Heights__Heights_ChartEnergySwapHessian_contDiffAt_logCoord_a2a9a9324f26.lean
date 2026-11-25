-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiffAt_logCoord_a2a9a9324f26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:33.923664+00:00
-- url     : https://prove2.me/submissions/edf948d9-b917-4ac0-8376-8029e5da4574

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
theorem _root_.solution {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 (logCoord y) y := by
  have hmem : y 0 / y 0 ∈ Complex.slitPlane := by
    rw [div_self hy]
    exact Complex.one_mem_slitPlane
  exact ((Complex.contDiffAt_log hmem).comp y
    ((contDiff_apply ℂ ℂ (0 : Fin (e + 1))).contDiffAt.div_const (y 0))).add contDiffAt_const
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
