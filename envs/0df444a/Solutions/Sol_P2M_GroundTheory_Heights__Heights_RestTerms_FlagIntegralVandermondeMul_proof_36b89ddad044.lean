-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagIntegralVandermondeMul_proof_36b89ddad044
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:08:36.056293+00:00
-- url     : https://prove2.me/submissions/565971a7-a17e-4608-91cc-3cd9b5fad885

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralVandermondeMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_flagIntegral_C_mul_710bd134373c


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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagIntegralVandermondeMul
theorem _root_.solution (h1 : FlagIntegralTopComponent.Statement)
    (h2 : FlagHomogeneousComponentMul.Statement) (h3 : FlagVandermondeHomogeneous.Statement) :
    FlagIntegralVandermondeMul.Statement := by
  intro f N R
  rw [h1 f N (blockVandermonde f N * R),
    h2 _ (blockVandermonde f N) R (topDegree f N) (topDegree f N) (h3 f N),
    if_pos le_rfl, Nat.sub_self, homogeneousComponent_zero, mul_comm,
    Flag.flagIntegral_C_mul, constantCoeff_eq]
end FlagIntegralVandermondeMul
end GroundTheory.Heights₂.Heights.RestTerms
