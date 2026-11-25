-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_proof_f67de1c4e35c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:56:34.162747+00:00
-- url     : https://prove2.me/submissions/2f913619-5191-4edb-822e-21a759e6c9a6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_isDegZeroSmooth_rho_f620d4c5f71e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_sum_rho_22f6900690fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_rho_eq_zero_f7e1fc5f243f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (segre)
namespace GroundTheory.Heights₂.Heights
namespace SegrePartition
theorem _root_.solution : SegrePartition.Statement := by
  intro K _ _ ι _ hne
  have hN : 0 < SegrePartition.numIdx ι := by
    rw [SegrePartition.numIdx, Nat.cast_pos]
    exact Fintype.card_pos
  exact ⟨(Real.sqrt (2 * SegrePartition.numIdx ι))⁻¹,
    inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)), SegrePartition.rho,
    SegrePartition.isDegZeroSmooth_rho hN, SegrePartition.sum_rho hN,
    SegrePartition.rho_eq_zero hN⟩
end SegrePartition
end GroundTheory.Heights₂.Heights
