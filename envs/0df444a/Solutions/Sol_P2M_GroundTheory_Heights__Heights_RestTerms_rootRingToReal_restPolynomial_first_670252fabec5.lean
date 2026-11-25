-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_restPolynomial_first_670252fabec5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:24.314546+00:00
-- url     : https://prove2.me/submissions/64f6ea5f-52d2-4ec1-8d6d-18bbef6ec386

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_first_18648e576495
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_first_dadd076ac59a

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
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (restPolynomial f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.restPoly f r a false := by
  rw [restPolynomial, IndefiniteRowSideFullHecke.RestTerms.restPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first,
    rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]
end GroundTheory.Heights₂.Heights.RestTerms
