-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SegrePartition_contDiff_segreSqSum_2a999fd991c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:15:59.902469+00:00
-- url     : https://prove2.me/submissions/72c72bf5-9ce8-43a6-8583-60571f99d7d0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_contDiff_segreSq_aac3f18011a5

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
theorem _root_.solution :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segreSqSum z) :=
  ContDiff.sum fun i _ => contDiff_segreSq i
end GroundTheory.Heights₂.Heights.SegrePartition
