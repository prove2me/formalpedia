-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagIntegralKillsPowerSums_intersectionNumber_baseChange_c9e02b906a68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:29.303911+00:00
-- url     : https://prove2.me/submissions/6e998e85-7d1c-4faf-a1d2-db3191680daf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AntisymmetrizeBlockVandermondeOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_DividedDifferenceVandermonde_flagIntegral_eq_mul_ddConst_53ddae8e92d5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagEq_ddConst_psumAt_mul_5fb3aa7ed198
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_blockPowerSum_8334d045ed2f


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
open DividedDifferenceVandermonde
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagIntegralKillsPowerSums
theorem _root_.solution : FlagIntegralKillsPowerSums.Statement := by
  intro f N k τ G hk _
  have h := flagIntegral_eq_mul_ddConst f N N 0 rfl (blockPowerSum f N k τ * G)
  rw [map_mul, rootRingToReal_blockPowerSum, FlagEq.ddConst_psumAt_mul _ _ _ _ _ _ hk,
    mul_zero] at h
  exact_mod_cast h
end FlagIntegralKillsPowerSums
end GroundTheory.Heights₂.Heights.RestTerms
