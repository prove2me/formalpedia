-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentJacComp_real_inner_eq_re_595de423dd88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:02.036111+00:00
-- url     : https://prove2.me/submissions/990b1527-c7ee-41a9-a44d-b1f3b6443958

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentJacComp

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
namespace GroundTheory.Heights₂.Heights
namespace TangentJacComp
theorem _root_.solution {d : ℕ} (x y : EuclideanSpace ℂ (Fin d)) :
    @inner ℝ _ _ x y = RCLike.re (@inner ℂ _ _ x y) := by
  simp [PiLp.inner_apply, Complex.inner, map_sum]
end TangentJacComp
end GroundTheory.Heights₂.Heights
