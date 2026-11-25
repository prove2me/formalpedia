-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_flagIntegral_add_smul_15ff1eab2e68
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:52:34.831877+00:00
-- url     : https://prove2.me/submissions/7e786ffc-f6aa-4743-afff-b49228397762

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealTransferOfSyzygy

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
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
namespace GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
theorem _root_.solution (f N : ℕ) (A B : RootRing f N) (t : ℚ) :
    flagIntegral f N (A + t • B) = flagIntegral f N A + t * flagIntegral f N B := by
  rw [flagIntegral, flagIntegral, flagIntegral, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [coeff_add, coeff_smul, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq
