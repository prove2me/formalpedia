-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartEnergyInvariance_invariantUnder_of_mul_right_3611512dcdae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:36:26.772587+00:00
-- url     : https://prove2.me/submissions/247f984d-ac67-4539-ad2d-d809d189913d

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
theorem _root_.solution {C V : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ}
    (hCV : EnergyInvariantUnder (C * V)) (hV : EnergyInvariantUnder V) (hC : C.det ≠ 0) :
    EnergyInvariantUnder C := by
  intro M N hM hN k
  rw [← hV _ _ (posDef_conj hM hC) (posDef_conj hN hC), ← conj_mul, ← conj_mul, hCV M N hM hN]
end GroundTheory.Heights₂.Heights.ChartEnergyInvariance
