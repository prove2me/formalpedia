-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestPolynomialHomogeneousDecomposition_proof_5df9701c2be8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:08:37.212665+00:00
-- url     : https://prove2.me/submissions/e54af3ce-ce3e-4c5c-bde1-0879716c4e9d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneousDecomposition

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
namespace RestPolynomialHomogeneousDecomposition
theorem _root_.solution (h1 : CoinvAboveTop.Statement)
    (h2 : RestPolynomialHomogeneous.Statement) :
    RestPolynomialHomogeneousDecomposition.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, hF⟩ := h1 ℚ f (r + a) (topDegree f (r + a) + 1) (restPolynomial f r a c)
    (h2 f r a c) (by unfold Coinv.coinvTop topDegree; omega)
  exact ⟨Q, hF, hQ⟩
end RestPolynomialHomogeneousDecomposition
end GroundTheory.Heights₂.Heights.RestTerms
