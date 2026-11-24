-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagRestrictPowerSum_proof_58dcffbf3388
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:08:30.822168+00:00
-- url     : https://prove2.me/submissions/4af2bfb5-e73b-4860-8fe3-f37e14e40f29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagRestrictPowerSum

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagRestrictPowerSum
theorem _root_.solution : FlagRestrictPowerSum.Statement := by
  intro f N k τ σ hk
  have hk0 : k ≠ 0 := by omega
  unfold blockPowerSum restrictToBlock
  simp only [map_sum, map_pow, aeval_X]
  split_ifs with h
  · subst h
    simp [psum]
  · simp [zero_pow hk0]
end FlagRestrictPowerSum
end GroundTheory.Heights₂.Heights.RestTerms
