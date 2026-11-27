-- Prove2me | solution 1 for UnitBallK.mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:33:47.427588+00:00
-- url     : https://prove2.me/submissions/2bdc64cc-9eb9-4b79-a022-669d77e05860

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneInverseMembership_UnitBallK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UnitBallK
variable (K : Type*) [NormedField K] [IsUltrametricDist K]
variable {K}
namespace UnitBallK
theorem _root_.solution {x y : K} (hx : x ∈ subring K) (hy : y ∈ subring K) : x * y ∈ subring K :=
  (subring K).mul_mem hx hy
end UnitBallK
