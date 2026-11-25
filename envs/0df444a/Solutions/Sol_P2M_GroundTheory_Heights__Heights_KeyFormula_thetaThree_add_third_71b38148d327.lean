-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_third_71b38148d327
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:29:41.644837+00:00
-- url     : https://prove2.me/submissions/b304ab01-413f-4917-bc22-a20103ae89d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent

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
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution (ν : ℕ) (w : ℂ) : thetaThree ν (w + 1 / 3) = zeta3 ^ ν * thetaThree ν w := by
  unfold thetaThree zeta3
  rw [show 3 * (w + 1 / 3) + ν * I = (3 * w + ν * I) + 1 by ring, jacobiTheta₂_add_left,
    ← Complex.exp_nat_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2; ring
end GroundTheory.Heights₂.Heights.KeyFormula
