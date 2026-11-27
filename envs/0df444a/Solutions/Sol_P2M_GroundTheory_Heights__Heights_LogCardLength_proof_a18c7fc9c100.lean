-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogCardLength_proof_a18c7fc9c100
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:01.747082+00:00
-- url     : https://prove2.me/submissions/717e35cc-e46d-4bd6-9535-832699cf8565

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLogCardLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_logCardLength_main_93130c21e0ca

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
noncomputable section
open logCardLength
namespace GroundTheory.Heights₂.Heights
namespace LogCardLength
theorem _root_.solution : LogCardLength.Statement := by
  intro R _ N _ _ _
  exact (main (Nat.card N) N rfl).2.2
end LogCardLength
end GroundTheory.Heights₂.Heights
