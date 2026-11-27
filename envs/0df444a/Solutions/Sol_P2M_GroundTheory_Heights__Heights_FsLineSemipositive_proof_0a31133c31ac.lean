-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FsLineSemipositive_proof_0a31133c31ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:04.99318+00:00
-- url     : https://prove2.me/submissions/e0f75f8d-9207-491e-a661-3d291c205fd6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PFsLineSemipositive

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
namespace GroundTheory.Heights₂.Heights
namespace FsLineSemipositive
theorem _root_.solution (h₁ : FsLineSmooth.Statement) (h₂ : FsLineLevi.Statement) :
    FsLineSemipositive.Statement := by
  intro K _ ι _ P
  exact ⟨h₁ K ι, fun z hz w _ => h₂ K ι z w hz.1⟩
end FsLineSemipositive
end GroundTheory.Heights₂.Heights
