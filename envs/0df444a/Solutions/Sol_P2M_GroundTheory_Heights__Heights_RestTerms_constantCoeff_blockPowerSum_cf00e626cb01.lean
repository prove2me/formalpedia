-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_constantCoeff_blockPowerSum_cf00e626cb01
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:12:06.772109+00:00
-- url     : https://prove2.me/submissions/7a70f6a4-61a2-4597-9f16-226ce14290d9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralKillsPowerSums

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
theorem _root_.solution (f N k : ℕ) (τ : Fin f) (hk : 1 ≤ k) :
    constantCoeff (blockPowerSum f N k τ) = 0 := by
  simp [blockPowerSum, map_sum, map_pow, constantCoeff_X, zero_pow (show k ≠ 0 by omega)]
end GroundTheory.Heights₂.Heights.RestTerms
