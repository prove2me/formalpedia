-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallPowerSum_first_349a4d00b92e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:40:09.641627+00:00
-- url     : https://prove2.me/submissions/4cc90440-bc8a-46da-8957-ebacad9a2ce8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_X_6be993a34174
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_C_43a59c7a9997
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Heights₂.Heights.RestTerms.rootRingToReal_X
attribute [local simp] GroundTheory.Heights₂.Heights.RestTerms.rootRingToReal_C

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f r a m : ℕ) (τ : Fin f) :
    rootRingToReal f (r + a) r a rfl (smallPowerSum f r a .first m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f r a false m τ := by
  simp only [smallPowerSum, yRoot, SmallBlock.sign, yIndex, map_sum, map_pow, map_mul,
    rootRingToReal_C, rootRingToReal_X, IndefiniteRowSideFullHecke.RestTerms.smallPsum, Bool.false_eq_true, if_false,
    Rat.cast_neg, Rat.cast_one, C_neg, C_1, neg_one_mul, map_neg]
  refine sum_congr rfl fun i _ => ?_
  rfl
end GroundTheory.Heights₂.Heights.RestTerms
