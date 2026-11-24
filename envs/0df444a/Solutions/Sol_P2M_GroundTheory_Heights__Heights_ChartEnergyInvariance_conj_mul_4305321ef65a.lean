-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_conj_mul_4305321ef65a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:14.890423+00:00
-- url     : https://prove2.me/submissions/f4a43e48-bdc9-4dc6-917c-1163095ca6ab

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
theorem _root_.solution (M A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    (A * B)ᴴ * M * (A * B) = Bᴴ * (Aᴴ * M * A) * B := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]
end GroundTheory.Heights₂.Heights.ChartEnergyInvariance
