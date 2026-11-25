-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_perm_fin_two_univ_830315b3909e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:29.837798+00:00
-- url     : https://prove2.me/submissions/b89952c2-1d17-4670-b627-2f3fca1665d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by
  decide
end GroundTheory.Heights₂.Heights.LowerBoundFree
