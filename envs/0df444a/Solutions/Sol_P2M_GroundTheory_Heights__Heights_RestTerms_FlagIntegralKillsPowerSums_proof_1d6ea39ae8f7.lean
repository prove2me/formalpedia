-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagIntegralKillsPowerSums_proof_1d6ea39ae8f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:54:15.514581+00:00
-- url     : https://prove2.me/submissions/0380d486-d49d-4aef-86f1-e34abc04be71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralKillsPowerSums
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_constantCoeff_blockPowerSum_cf00e626cb01

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
namespace FlagIntegralKillsPowerSums
theorem _root_.solution (h1 : FlagDividedDifferencePoly.Statement)
    (h2 : FlagSymmetricMulAntisym.Statement) (h3 : FlagPowerSumSymmetric.Statement)
    (h4 : FlagIntegralViaQuotient.Statement) : FlagIntegralKillsPowerSums.Statement := by
  intro f N k τ G hk _
  obtain ⟨R, hR, -⟩ := h1 f N G
  have hA : antisymmetrize f N (blockPowerSum f N k τ * G) =
      blockVandermonde f N * (blockPowerSum f N k τ * R) := by
    rw [h2 f N _ G (h3 f N k τ), hR]
    ring
  rw [h4 f N _ _ hA, map_mul, constantCoeff_blockPowerSum f N k τ hk, zero_mul, mul_zero]
end FlagIntegralKillsPowerSums
end GroundTheory.Heights₂.Heights.RestTerms
