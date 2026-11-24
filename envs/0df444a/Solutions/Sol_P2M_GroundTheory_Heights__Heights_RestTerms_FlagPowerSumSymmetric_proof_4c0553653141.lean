-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagPowerSumSymmetric_proof_4c0553653141
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:08:43.470204+00:00
-- url     : https://prove2.me/submissions/7b6d5cad-0752-4bcb-80bd-78552f408be9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagPowerSumSymmetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_X_536c027402b7


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
namespace FlagPowerSumSymmetric
theorem _root_.solution : FlagPowerSumSymmetric.Statement := by
  intro f N k τ w
  simp only [blockPowerSum, map_sum, map_pow, Flag.blockPermute_X]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : RootRing f N) ^ k)
end FlagPowerSumSymmetric
end GroundTheory.Heights₂.Heights.RestTerms
