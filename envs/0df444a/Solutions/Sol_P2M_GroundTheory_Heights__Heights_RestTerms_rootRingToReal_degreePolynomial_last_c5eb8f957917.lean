-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_degreePolynomial_last_c5eb8f957917
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:13:21.572057+00:00
-- url     : https://prove2.me/submissions/5e683794-90b0-4f00-8671-179e6e7f9572

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHomogeneousComponentMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_smallBlockMu_last_5f162ecc6d85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootRingToReal_fibreClass_last_fe182079683b

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
    rootRingToReal f (r + a) a r (Nat.add_comm r a)
        (smallBlockMu f r a .last ^ (f * (r * a)) * fibreClass f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f a r true := by
  rw [IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_last,
    rootRingToReal_fibreClass_last, IndefiniteRowSideFullHecke.RestTerms.nDim, show f * a * r = f * (r * a) by ring]
end GroundTheory.Heights₂.Heights.RestTerms
