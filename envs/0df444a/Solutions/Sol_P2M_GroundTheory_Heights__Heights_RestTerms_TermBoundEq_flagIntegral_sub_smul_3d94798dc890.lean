-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_TermBoundEq_flagIntegral_sub_smul_3d94798dc890
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:53:00.020144+00:00
-- url     : https://prove2.me/submissions/44399b0c-2ece-4465-b951-b501980c44ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealRootRingToRealAlt

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
open GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
variable {σ : Type*} (φ : Module.Dual ℚ ℝ)
namespace GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
theorem _root_.solution (f N : ℕ) (A B : RootRing f N) (s : ℚ) :
    flagIntegral f N (A - s • B) = flagIntegral f N A - s * flagIntegral f N B := by
  rw [flagIntegral, flagIntegral, flagIntegral, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_smul, smul_eq_mul]
  ring
end GroundTheory.Heights₂.Heights.RestTerms.TermBoundEq
