-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaOneVar_ne_zero_a962d06be8ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:38.075874+00:00
-- url     : https://prove2.me/submissions/f8c1dbd8-5724-463a-a605-1fa454a003fb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaOneVar_zero_ne_0e0ead3edf8d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution : thetaOneVar ≠ 0 := fun h => thetaOneVar_zero_ne (by rw [h]; rfl)
end GroundTheory.Heights₂.Heights.KeyFormula
