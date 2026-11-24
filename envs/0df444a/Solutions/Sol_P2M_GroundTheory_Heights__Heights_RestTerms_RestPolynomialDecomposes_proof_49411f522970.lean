-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_RestPolynomialDecomposes_proof_49411f522970
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:08:35.180798+00:00
-- url     : https://prove2.me/submissions/661cceb6-5e8b-477e-a385-8ddbdcf4cbc6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialDecomposes

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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace RestPolynomialDecomposes
theorem _root_.solution (h1 : RestPolynomialHomogeneousDecomposition.Statement) :
    RestPolynomialDecomposes.Statement := by
  intro f r a c
  obtain ⟨Q, hQ, -⟩ := h1 f r a c
  exact ⟨Q, hQ⟩
end RestPolynomialDecomposes
end GroundTheory.Heights₂.Heights.RestTerms
