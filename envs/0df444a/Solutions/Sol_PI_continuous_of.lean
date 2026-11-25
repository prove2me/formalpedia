-- Prove2me | solution 1 for PI.continuous_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:47.0642+00:00
-- url     : https://prove2.me/submissions/4e4f5ff5-2961-49b1-97fe-ef337b5f5e03

import Definitions.Def_Formalism_PeriodIntegrals_HaarDefs
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_ContinuousExpLie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff
noncomputable section
open PI
open Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace PI
theorem _root_.solution : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := continuous_id
end PI
