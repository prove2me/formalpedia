-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FsLineSmooth_proof_04d97fb10246
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:55:25.399857+00:00
-- url     : https://prove2.me/submissions/335584f3-fc27-4911-873c-0a191e9444bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PFsLineSmooth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FubiniStudySmooth_contDiffAt_blockNorm_76253190e502

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
open ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights
namespace FsLineSmooth
theorem _root_.solution : FsLineSmooth.Statement := by
  intro K _ ι _
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : (Σ k, ι k) → ℂ => ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ ^ ((1 : K → ℤ) k)) _
  refine contDiffOn_prod fun k _ => ?_
  intro z hz
  simp only [Pi.one_apply, zpow_one]
  exact (FubiniStudySmooth.contDiffAt_blockNorm ι k z (hz k)).contDiffWithinAt
end FsLineSmooth
end GroundTheory.Heights₂.Heights
