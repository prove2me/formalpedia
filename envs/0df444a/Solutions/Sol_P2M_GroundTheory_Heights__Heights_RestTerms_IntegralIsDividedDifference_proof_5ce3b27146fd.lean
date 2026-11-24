-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_IntegralIsDividedDifference_proof_5ce3b27146fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:28.410066+00:00
-- url     : https://prove2.me/submissions/0f4562fb-cc3c-4aac-a859-e873d81ba51d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PIntegralIsDividedDifference

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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace IntegralIsDividedDifference
theorem _root_.solution (h1 : FlagIntegralTopDegree.Statement)
    (h2 : FlagIntegralVandermondePos.Statement) : IntegralIsDividedDifference.Statement := by
  intro f N
  refine ⟨flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f, ?_, ?_⟩
  · exact div_ne_zero (h2 f N).ne' (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)))
  · intro H hH
    exact h1 f N H hH
end IntegralIsDividedDifference
end GroundTheory.Heights₂.Heights.RestTerms
