-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchBlockVandermondeOne_proof_5b66cc37c276
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:08:42.41646+00:00
-- url     : https://prove2.me/submissions/c14e6710-716d-43f9-9180-37b9c0bc42f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchBlockVandermondeOne

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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchBlockVandermondeOne
theorem _root_.solution : SchBlockVandermondeOne.Statement := by
  intro N
  simp only [blockVandermonde, vandermondeOf, Fin.prod_univ_one, map_prod, map_sub, rename_X]
end SchBlockVandermondeOne
end GroundTheory.Heights₂.Heights.RestTerms
