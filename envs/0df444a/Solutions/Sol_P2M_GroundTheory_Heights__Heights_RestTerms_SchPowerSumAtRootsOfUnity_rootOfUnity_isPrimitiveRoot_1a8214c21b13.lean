-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchPowerSumAtRootsOfUnity_rootOfUnity_isPrimitiveRoot_1a8214c21b13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:52:36.750873+00:00
-- url     : https://prove2.me/submissions/f857579b-b6f7-4e4f-abb1-6056dfbe122c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchPowerSumAtRootsOfUnity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchPowerSumAtRootsOfUnity
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) : IsPrimitiveRoot (rootOfUnity k) k := by
  simpa [rootOfUnity] using Complex.isPrimitiveRoot_exp k (by omega)
end SchPowerSumAtRootsOfUnity
end GroundTheory.Heights₂.Heights.RestTerms
