-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LinesGenIndexPi_proof_f2bf82a31706
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:19.412666+00:00
-- url     : https://prove2.me/submissions/a9987776-9a64-4db0-a4f5-0c713d17a906

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesGenIndexPi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGenIndexPi_relIndex_pi_ee181e7e4ed0

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
namespace LinesGenIndexPi
theorem _root_.solution : LinesGenIndexPi.Statement := by
  intro η _ G _ A B
  unfold genIndex
  rw [KLinesGenIndexPi.relIndex_pi, KLinesGenIndexPi.relIndex_pi, Nat.cast_prod, Nat.cast_prod,
    ← Finset.prod_div_distrib]
end LinesGenIndexPi
end GroundTheory.Heights₂.Heights
