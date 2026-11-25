-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_hermChartPot_586ea6d2fcc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:36.864069+00:00
-- url     : https://prove2.me/submissions/58caec11-6f0a-474e-89fd-06dd6af3b7b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartHessHolo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartDensityIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergySwap
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergySwapHessian_contDiff_gbPot_b72516f9b53b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartDensityIntegrableAlt_hermChartPot_eq_gbPot_affine_4211beb1f02e


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
theorem _root_.solution (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ContDiff ℝ 2 (hermChartPot M) := by
  obtain ⟨c, P, κ, hP, hEq⟩ := ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM
  rw [hEq]
  exact (contDiff_gbPot.comp (contDiff_const.add (realCLE P hP).contDiff)).add contDiff_const
end GroundTheory.Heights₂.Heights.ChartEnergySwapHessian
