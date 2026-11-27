-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeTubeVolume_proof_3d198a379a6e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:29.623111+00:00
-- url     : https://prove2.me/submissions/6de9677d-7fd8-4b02-8e02-0e4231ff6cd1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeTubeVolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyMassLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSmallSetBallCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeTubeVolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_primeTube_exists_dim_0fd17737f684
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_primeTube_exact_28d603f75be1

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
open MvPolynomial MeasureTheory ComplexSets Metric
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PrimeTubeVolume
theorem _root_.solution (hL : VarietyMassLower.Statement) (hM : MassFinite.Statement) :
    PrimeTubeVolume.Statement := by
  intro n k J K hJ hk hK
  obtain ⟨d, hdk, hd⟩ := primeTube_exists_dim hJ hk
  obtain ⟨C, hC, hCr⟩ := primeTube_exact hL hM hJ hd hK
  refine ⟨C, hC, fun r hr => (hCr r hr).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC))⟩
  exact zpow_le_zpow_right_of_le_one₀ hr.1 hr.2 (by omega)
end PrimeTubeVolume
end GroundTheory.Heights₂.Heights
