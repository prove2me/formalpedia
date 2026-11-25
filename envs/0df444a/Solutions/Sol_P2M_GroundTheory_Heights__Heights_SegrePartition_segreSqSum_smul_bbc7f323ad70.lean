-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_segreSqSum_smul_bbc7f323ad70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:06:50.855661+00:00
-- url     : https://prove2.me/submissions/f0932632-f0dc-41aa-9a19-3c78e9f036ec

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_segreSq_smul_2910a77fc6d2

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
open GroundTheory.Heights₂.Heights.SegrePartition
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.SegrePartition
theorem _root_.solution (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segreSqSum (fun p => c p.1 * z p) = ‖∏ k, c k‖ ^ 2 * segreSqSum z := by
  simp only [segreSqSum, segreSq_smul, Finset.mul_sum]
end GroundTheory.Heights₂.Heights.SegrePartition
