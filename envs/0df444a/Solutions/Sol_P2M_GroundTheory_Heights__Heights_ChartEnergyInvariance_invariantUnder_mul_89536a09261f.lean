-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_mul_89536a09261f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:25.002693+00:00
-- url     : https://prove2.me/submissions/5b09a579-0720-4b39-9ed6-3738f5688a5b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergyInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartEnergySwap
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ChartMassAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartMassInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PChartEnergyInvariant
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_posDef_conj_008f736c5fcc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_conj_mul_4305321ef65a

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
theorem _root_.solution {A B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hA : EnergyInvariantUnder A)
    (hB : EnergyInvariantUnder B) (hAdet : A.det ≠ 0) : EnergyInvariantUnder (A * B) := by
  intro M N hM hN k
  rw [conj_mul, conj_mul, hB _ _ (posDef_conj hM hAdet) (posDef_conj hN hAdet), hA M N hM hN]
end GroundTheory.Heights₂.Heights.ChartEnergyInvariance
