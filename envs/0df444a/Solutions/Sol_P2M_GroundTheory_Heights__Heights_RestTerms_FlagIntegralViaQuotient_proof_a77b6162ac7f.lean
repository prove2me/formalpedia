-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagIntegralViaQuotient_proof_a77b6162ac7f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:08:41.085187+00:00
-- url     : https://prove2.me/submissions/02dae24a-b9be-47a1-adcf-6a9667025ac6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralViaQuotient

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
namespace FlagIntegralViaQuotient
theorem _root_.solution (h1 : FlagIntegralAntisymmetrize.Statement)
    (h2 : FlagIntegralVandermondeMul.Statement) : FlagIntegralViaQuotient.Statement := by
  intro f N H R hR
  have hA := h1 f N H
  rw [hR, h2 f N R] at hA
  have hne : (N.factorial : ℚ) ^ f ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))
  rw [div_mul_eq_mul_div, eq_div_iff hne]
  linear_combination -hA
end FlagIntegralViaQuotient
end GroundTheory.Heights₂.Heights.RestTerms
