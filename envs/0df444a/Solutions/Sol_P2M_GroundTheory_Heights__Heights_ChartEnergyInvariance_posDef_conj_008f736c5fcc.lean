-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_posDef_conj_008f736c5fcc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:15.19403+00:00
-- url     : https://prove2.me/submissions/81277a8c-741a-46bb-a49c-0c0157eb8beb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyInvariant

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
open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.ChartEnergyInvariance
open ChartMongeAmpereAffineInvariance
variable {e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartEnergyInvariance
theorem _root_.solution {M C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hC : C.det ≠ 0) :
    (Cᴴ * M * C).PosDef :=
  hM.conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det C).mpr (isUnit_iff_ne_zero.mpr hC)))
end GroundTheory.Heights₂.Heights.ChartEnergyInvariance
