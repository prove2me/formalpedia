-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_first_99821be0665a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:15.552832+00:00
-- url     : https://prove2.me/submissions/fbaac3f7-1552-4b21-8e3d-4457f328fe47

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
    rootRingToReal f (r + a) r a rfl
        (smallBlockMu f r a .first ^ (f * (r * a)) * fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f r a false := by
  rw [IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first,
    rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]
end GroundTheory.Heights₂.Heights.RestTerms
