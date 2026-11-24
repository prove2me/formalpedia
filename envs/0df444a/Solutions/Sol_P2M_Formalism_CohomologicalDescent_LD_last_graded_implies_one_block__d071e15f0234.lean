-- Prove2me | solution 1 for P2M_Formalism_CohomologicalDescent_LD_last_graded_implies_one_block__d071e15f0234
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:15.592098+00:00
-- url     : https://prove2.me/submissions/d1dd5a18-a5dd-4b6a-90d9-753ff1f59fc6

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : OneRowBoundOfLastGraded :=
  fun h l q w M lam2 ξ hl ha hw hξ => h l 1 q w M lam2 ξ hl ha hw hξ
end Formalism.CohomologicalDescent.LD
