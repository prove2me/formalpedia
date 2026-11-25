-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_chowFormHomog_a99a41068f23
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:40.160085+00:00
-- url     : https://prove2.me/submissions/6f000337-598a-488e-b518-4e09d85faf2f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowFormHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
variable {F : Type} [Field F] {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution : ChowFormHomog.Statement := ChowFormHomog.proof
end GroundTheory.Heights₂.Heights.Vertical
